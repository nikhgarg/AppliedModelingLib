import GN21DriverSurgePricing.ProofBridge

namespace GN21DriverSurgePricing

namespace PaperInterface

open ProofBridge
open MeasureTheory
open scoped ENNReal

/-! ## Source-model definitions -/

/-- Source-facing semantic target for the paper's single definition of
incentive-compatible pricing.  The source gives both the single-state and
two-state accept-all readings in one clause, so they are reviewed together as
one paper claim rather than as duplicate definition cards. -/
def review_definition_incentive_compatibleSpec :
    (SingleStateReward → Prop) × (DynamicReward → Prop) :=
  (fun R =>
    ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
      R σ ≤ R acceptAllPolicy,
   fun R =>
    dynamicFeasibleOpenPolicy acceptAllDynamicPolicy ∧
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy σ →
          R σ ≤ R acceptAllDynamicPolicy)

/-- Source-facing semantic target for the definition `review_definition_surge_state`. -/
def review_definition_surge_stateSpec
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (w : Fin 2 → PricingFunction) : Prop :=
  ∃ σ2 : TripPolicy,
    σ2 ⊆ acceptAllPolicy ∧ IsOpen σ2 ∧
      ∀ σ1 : TripPolicy,
        σ1 ⊆ acceptAllPolicy → IsOpen σ1 →
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) σ1 <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) σ2

/-! ## Main-text results -/

/-- Source-facing semantic target for `review_theorem1_single_state_threshold_best_response`. -/
def review_theorem1_single_state_threshold_best_responseSpec
  (μ : MeasureTheory.Measure TripLength) (arrivalRate : ℝ) (w : GN21PayoutFunction)
  (hrate_measurable : Measurable fun τ => w.toPricingFunction τ / τ)
  (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll :
    MeasureTheory.IntegrableOn w.toPricingFunction acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ) (hlambda : 0 < arrivalRate) : Prop :=
  ∃ c, 0 ≤ c ∧ ∃ σ,
    thresholdRatePolicy w.toPricingFunction c σ ∧
      singleStateMeasurableOptimal
        (singleStateRenewalReward μ arrivalRate w.toPricingFunction) σ

/-- Source-facing semantic target for `review_proposition3_1_affine_single_state_ic`. -/
def review_proposition3_1_affine_single_state_icSpec (mu : MeasureTheory.Measure TripLength)
  (arrivalRate m a : ℝ)
  (haccept_mass : singleStateTripMass mu acceptAllPolicy = 1)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy mu)
  (hlambda : 0 < arrivalRate) (ha_nonneg : 0 ≤ a)
  (ha_le_wait_value : a ≤ m / arrivalRate) : Prop :=
  singleStateMeasurableIncentiveCompatible (affineSingleStateRenewalReward mu arrivalRate m a)

/-- Source-facing semantic target for `review_theorem2_multiplicative_policy_shape_source_claim`. -/
def review_theorem2_multiplicative_policy_shape_source_claimSpec
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
      (fun i => multiplicativePricing (m i))) : Prop :=
  (∃ rho : Fin 2 → TripPolicy,
    dynamicOpenOptimal
        (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
        rho ∧
      rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
        rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1)) ∧
    ∀ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateMultiplicativeDynamicReward mu arrival switch12 switch21 m)
          rho →
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
          rejectsShortTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 1) (rho 1)

/-- Source-facing semantic target for `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states`. -/
def review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_statesSpec : Prop :=
  (((0 < (2 : ℝ) ∧
      rejectsLongTrips 2 (theorem2BothStatesContinuousNonsurgeDeviation 0)) ∧
    dynamicProfitableDeviation
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
        theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
      theorem2BothStatesContinuousNonsurgeDeviation) ∧
    ((0 < (2 : ℝ) ∧
        rejectsShortTrips 2 (theorem2BothStatesContinuousSurgeDeviation 1)) ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
          theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))
        theorem2BothStatesContinuousSurgeDeviation)) ∧
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional theorem2BothStatesContinuousMu
        theorem2BothStatesContinuousArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
        (fun i => multiplicativePricing (theorem2BothStatesContinuousM i)))

/-- Source-facing semantic target for `review_lemma1_measured_dynamic_reward_decomposition`. -/
def review_lemma1_measured_dynamic_reward_decompositionSpec
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {wI wJ : PricingFunction} {sigmaI sigmaJ : TripPolicy}
    (C : GN21DynamicIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ) : Prop :=
  ∀ᵐ omega ∂POmega,
    Filter.Tendsto
      (fun n : ℕ =>
        ((∑ k ∈ Finset.range n, C.stateEarningI k omega) +
            (∑ k ∈ Finset.range n, C.stateEarningJ k omega)) /
          ((∑ k ∈ Finset.range n, C.stateTimeI k omega) +
            (∑ k ∈ Finset.range n, C.stateTimeJ k omega)))
      Filter.atTop
      (nhds
        (gn21MeasuredDynamicReward muI muJ arrivalI arrivalJ switchIJ
          switchJI wI wJ sigmaI sigmaJ))

/-- Source-facing semantic target for `review_lemma2_switch_probability_formula`. -/
def review_lemma2_switch_probability_formulaSpec (lambdaIJ lambdaJI s : ℝ) : Prop :=
  gn21SwitchProb lambdaIJ lambdaJI s = lambdaIJ / (lambdaIJ + lambdaJI) * (1 - Real.exp (-(lambdaIJ + lambdaJI) * s))

/-- Source-facing semantic target for `review_lemma3_measured_time_fraction_formula`. -/
def review_lemma3_measured_time_fraction_formulaSpec
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {sigmaI sigmaJ : TripPolicy}
    (C : GN21TimeFractionIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ) : Prop :=
  ∀ᵐ omega ∂POmega,
    Filter.Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n, C.stateTimeI k omega) /
          ((∑ k ∈ Finset.range n, C.stateTimeI k omega) +
            (∑ k ∈ Finset.range n, C.stateTimeJ k omega)))
      Filter.atTop
      (nhds
        (gn21MeasuredTimeFraction muI muJ arrivalI arrivalJ switchIJ
          switchJI sigmaI sigmaJ))

/-- Source-facing semantic target for Theorem 3.  The paper presents the
general structured-policy clause and its stricter fully-IC clause as one
numbered theorem; both clauses therefore appear in one semantic target. -/
def review_theorem3_structured_pricingSpec : Prop :=
  (∀ (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
      (R1 : NNReal) (R2 switch12 switch21 : ℝ)
      [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
      [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
      (hR1_lt_R2 : (R1 : ℝ) < R2)
      (harrival1_pos : 0 < arrival 0) (harrival2_pos : 0 < arrival 1)
      (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
      (htime1_integrable :
        IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
      (htime2_integrable :
        IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
      (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
      (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1),
      ∃ m z : Fin 2 → ℝ, ∃ rho : Fin 2 → TripPolicy,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
          gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              acceptAllPolicy = R1 ∧
          gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              acceptAllPolicy = R2 ∧
          rho 1 = acceptAllPolicy ∧
          rejectsLongTripsFiniteOrInfiniteCutoff (rho 0) ∧
          dynamicOpenOptimal
            (gn21AggregateCTMCStructuredDynamicReward
              mu arrival switch12 switch21 m z)
            rho) ∧
  (∀ (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
      (R1 R2 switch12 switch21 : ℝ)
      [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
      [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
      (hR2_pos : 0 < R2)
      (hC_lt_ratio :
        theorem3FeasibilityThresholdC
            (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
            (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
            switch12 < R1 / R2)
      (hratio_lt_one : R1 / R2 < 1)
      (harrival1_pos : 0 < arrival 0) (harrival2_pos : 0 < arrival 1)
      (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
      (htime1_integrable :
        IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
      (htime2_integrable :
        IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
      (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
      (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1),
      ∃ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
          gn21MeasuredStateRewardRate (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              acceptAllPolicy = R1 ∧
          gn21MeasuredStateRewardRate (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              acceptAllPolicy = R2 ∧
          dynamicOpenOptimal
            (gn21AggregateCTMCStructuredDynamicReward
              mu arrival switch12 switch21 m z)
            acceptAllDynamicPolicy ∧
          ∀ rho : Fin 2 → TripPolicy,
            dynamicOpenOptimal
              (gn21AggregateCTMCStructuredDynamicReward
                mu arrival switch12 switch21 m z)
              rho →
              dynamicAcceptAllAlmostEverywhere mu rho)

/-! ## Appendix results -/

/-- Source-facing semantic target for `review_lemma4_single_state_threshold_uniqueness`. -/
def review_lemma4_single_state_threshold_uniquenessSpec (μ : MeasureTheory.Measure TripLength)
  (arrivalRate : ℝ) (w : PricingFunction) (hrate_measurable : Measurable fun τ => w τ / τ)
  (hrate_nonneg : ∀ (τ : TripLength), 0 < τ → 0 ≤ w τ / τ) (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll : MeasureTheory.IntegrableOn w acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ) (hlambda : 0 < arrivalRate) : Prop :=
  ∃ cstar,
    0 ≤ cstar ∧
      ∃ σstar,
        thresholdRatePolicy w cstar σstar ∧
          singleStateRenewalReward μ arrivalRate w σstar = cstar ∧
            singleStateMeasurableOptimal (singleStateRenewalReward μ arrivalRate w) σstar ∧
              ∀ ρ ⊆ acceptAllPolicy,
                MeasurableSet ρ →
                  singleStateMeasurableOptimal (singleStateRenewalReward μ arrivalRate w) ρ →
                    singleStateTripMass μ (strictThresholdPolicy w cstar \ ρ) = 0 ∧
                      singleStateTripMass μ (ρ \ completeThresholdPolicy w cstar) = 0

/-- Source-facing semantic target for `lemma5_full_variational_policy_forms`. -/
def lemma5_full_variational_policy_formsSpec
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
      mu Rhat response shape sigma margin) : Prop :=
  ∃ policy : TripPolicy,
    lemma5SourcePolicyForm shape policy ∧
      Rhat sigma ≤ Rhat policy ∧
      (¬ lemma5SourcePolicyFormAlmostEverywhere mu shape sigma →
        Rhat sigma < Rhat policy)

/-- Source-facing semantic target for `review_lemma6_upper_endpoint_derivative_formula`. -/
def review_lemma6_upper_endpoint_derivative_formulaSpec
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
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u) : Prop :=
  HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb x) Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density x) Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment x) Wj)
      (arrivalRate * density u * Qj *
          gn21DerivativeSignKernel (switchProb u) u (payment u)
            (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
            (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj
            (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u) Wj /
        (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
            Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u) ^
          2)
      u ∧
    (0 < density u →
      sameStrictSign
        (arrivalRate * density u * Qj *
            gn21DerivativeSignKernel (switchProb u) u (payment u)
              (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
              (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj
              (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u) Wj /
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
              Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u) ^
            2)
        (gn21Lemma6Response (switchProb u) u (payment u)
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u) Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u) Tj Ri Rj))

/-- Source-facing semantic target for `review_lemma7_affine_positive_additive_response_quasi_convex`. -/
def review_lemma7_affine_positive_additive_response_quasi_convexSpec
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_pos : 0 < a) (hdelta_ji_nonpos : Rj - Ri ≤ 0)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) : Prop :=
  strictQuasiConvexOnPositive fun u =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a) Qi Qj Ti Tj Ri Rj

/-- Source-facing semantic target for `review_lemma8_affine_negative_additive_response_quasi_concave`. -/
def review_lemma8_affine_negative_additive_response_quasi_concaveSpec
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_neg : a < 0) (hdelta_ji_nonneg : 0 ≤ Rj - Ri)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) : Prop :=
  strictQuasiConcaveOnPositive fun u =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a) Qi Qj Ti Tj Ri Rj

/-- Source-facing semantic target for `review_lemma9_surge_derivative_positive_of_acceptAll_bounds`. -/
def review_lemma9_surge_derivative_positive_of_acceptAll_boundsSpec
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
  (hgap_le : switch21 * T2 - Q2 ≤ switch21 * Tbar2 - Qbar2) (hswitch_lt_Q2 : switch21 < Q2) (hQ2_le : Q2 ≤ Qbar2) : Prop :=
  0 <
    (lemma6EndpointDerivativeData_of_interval_density_paths arrivalRate switch21 lowerEndpoint u Q1 T1 (R1 * T1) density
        (gn21SwitchProb switch21 switch12) (ctmcStructuredSurgePrice m z switch21 switch12) harrival_pos hdensity_pos
        hQ1_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont).derivativeValue

/-- Source-facing semantic target for `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds`. -/
def review_lemma10_nonsurge_derivative_positive_of_acceptAll_boundsSpec
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
  (hswitch_lt_Q1 : switch12 < Q1) (hQ1_le : Q1 ≤ Qbar1) : Prop :=
  0 <
    (lemma6EndpointDerivativeData_of_interval_density_paths arrivalRate switch12 lowerEndpoint u Q2 T2 (R2 * T2) density
        (gn21SwitchProb switch12 switch21) (ctmcStructuredSurgePrice R2 z switch12 switch21) harrival_pos hdensity_pos
        hQ2_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont).derivativeValue

/-- Source-facing semantic target for `review_theorem4_full_structural_policy_forms_direct`. -/
def review_theorem4_full_structural_policy_forms_directSpec
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
                  (Function.update rho i policy)) tau) : Prop :=
  (∃ rho : Fin 2 → TripPolicy,
    dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho ∧
      lemma5SourcePolicyForm (shape 0) (rho 0) ∧
        lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
    ∀ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho →
        lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) ∧
          lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1)



end PaperInterface
end GN21DriverSurgePricing
