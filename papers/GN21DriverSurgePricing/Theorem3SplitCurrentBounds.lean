import GN21DriverSurgePricing.DomainBridge

/-!
# Theorem 3 Split Current-Bounds Routes

This file contains the thin Theorem 3 bridge layer that is useful for
iteration and multi-agent work: feasible current-bounds data prove weak IC,
while optimal-policy positive-response data prove a.e. uniqueness.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

/--
Converse direction of the scaled reward-rate bridge: if the Appendix-D scaled
earning identity has already been proved, then the measured reward rate is the
named scalar.
-/
theorem gn21MeasuredStateRewardRate_eq_of_scaled_earning
    (μ : Measure TripLength) (arrivalRate rewardRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ ≠ 0)
    (harrivalMass : arrivalRate * singleStateTripMass μ σ ≠ 0)
    (hscaledTime : gn21ScaledStateTime μ arrivalRate σ ≠ 0)
    (hscaled :
      gn21ScaledStateEarning μ arrivalRate w σ =
        rewardRate * gn21ScaledStateTime μ arrivalRate σ) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ = rewardRate := by
  rw [gn21MeasuredStateRewardRate_eq_scaled_primitives
    μ arrivalRate w σ hmass harrivalMass, hscaled]
  field_simp [hscaledTime]

/-!
## Source-data to reward-rate bridges

The older sequential current-bounds source records store the fixed-state reward
identity in Appendix-D scaled form.  The source-faithful Lemma 9/10 route below
uses the paper's local reward-rate notation, so these bridges convert the
scaled identity back to a measured reward-rate equality.
-/

/-- Convert non-surge Lemma 10 source data for a structured fixed surge price
to the reward-rate form used by the sequential positive-response route. -/
theorem GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_source_structured
    {μI μJ : Measure TripLength}
    {arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ : ℝ}
    {σI σJ : TripPolicy}
    (hfixed_mass : singleStateTripMass μJ σJ ≠ 0)
    (hfixed_arrival_mass : arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hfixed_time : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (D :
      GN21NonsurgeLemma10AcceptAllAggregateSourceData
        μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio
        (ctmcStructuredSurgePrice mJ zJ switch21 switch12) σI σJ) :
    GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
      μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ
      σI σJ where
  current_mass_pos := D.current_mass_pos
  bounds := D.bounds
  z_eq := D.z_eq
  R2_pos := D.R2_pos
  fixed_reward_rate :=
    gn21MeasuredStateRewardRate_eq_of_scaled_earning
      μJ arrivalJ R2 (ctmcStructuredSurgePrice mJ zJ switch21 switch12)
      σJ hfixed_mass hfixed_arrival_mass hfixed_time D.fixed_reward_rate

/--
Build non-surge Lemma 10 reward-rate data by tightening the accept-all
moving-state bounds to the current non-surge policy.  This is the reward-rate
analogue of `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening`.
-/
theorem GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_acceptAll_tightening
    {μI μJ : Measure TripLength}
    {arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ : ℝ}
    {σI σJ : TripPolicy}
    (hσI_subset : σI ⊆ acceptAllPolicy)
    (hσI_measurable : MeasurableSet σI)
    (harrivalI_pos : 0 < arrivalI)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htimeI_current_integrable :
      IntegrableOn (fun τ : TripLength => τ) σI μI)
    (hqI_current_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ) σI μI)
    (htimeI_acceptAll_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μI)
    (hqI_acceptAll_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy μI)
    (hbounds_acceptAll :
      lemma10StructuredBounds ratio
        (gn21ScaledStateTime μJ arrivalJ σJ)
        (gn21ExitWeightIntegral μJ arrivalJ switch21 switch12 σJ)
        (gn21ScaledStateTime μI arrivalI acceptAllPolicy)
        (gn21ExitWeightIntegral μI arrivalI switch12 switch21 acceptAllPolicy)
        switch12)
    (hfixed_A_pos :
      0 <
        gn21ScaledStateTime μJ arrivalJ σJ * switch12 +
          gn21ExitWeightIntegral μJ arrivalJ switch21 switch12 σJ)
    (hfixed_exit_nonneg :
      0 ≤ gn21ExitWeightIntegral μJ arrivalJ switch21 switch12 σJ)
    (hcurrent_mass_pos : 0 < singleStateTripMass μI σI)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hfixed_mass :
      singleStateTripMass μJ σJ ≠ 0)
    (hfixed_arrival_mass :
      arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hfixed_time :
      gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (hfixed_reward_rate :
      gn21MeasuredStateRewardRate μJ arrivalJ
        (ctmcStructuredSurgePrice mJ zJ switch21 switch12) σJ = R2) :
    GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
      μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ
      σI σJ := by
  have hfixed_scaled :
      gn21ScaledStateEarning μJ arrivalJ
          (ctmcStructuredSurgePrice mJ zJ switch21 switch12) σJ =
        R2 * gn21ScaledStateTime μJ arrivalJ σJ :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate
      μJ arrivalJ R2
      (ctmcStructuredSurgePrice mJ zJ switch21 switch12) σJ
      hfixed_mass hfixed_arrival_mass hfixed_time hfixed_reward_rate
  have Dsrc :
      GN21NonsurgeLemma10AcceptAllAggregateSourceData
        μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio
        (ctmcStructuredSurgePrice mJ zJ switch21 switch12) σI σJ :=
    GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening
      hσI_subset hσI_measurable harrivalI_pos hswitch12_pos
      hswitch21_pos htimeI_current_integrable hqI_current_integrable
      htimeI_acceptAll_integrable hqI_acceptAll_integrable hbounds_acceptAll
      hfixed_A_pos hfixed_exit_nonneg hcurrent_mass_pos hz hR2_pos
      hfixed_scaled
  exact
    GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_source_structured
      hfixed_mass hfixed_arrival_mass hfixed_time Dsrc

/-- Convert surge Lemma 9 source data for a structured fixed non-surge price
to the reward-rate form used by the sequential positive-response route. -/
theorem GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_source_structured
    {μI μJ : Measure TripLength}
    {arrivalI arrivalJ switch12 switch21 m R1 z ratio mI zI : ℝ}
    {σI σJ : TripPolicy}
    (hfixed_mass : singleStateTripMass μI σI ≠ 0)
    (hfixed_arrival_mass : arrivalI * singleStateTripMass μI σI ≠ 0)
    (hfixed_time : gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (D :
      GN21SurgeLemma9AcceptAllAggregateSourceData
        μI μJ arrivalI arrivalJ switch12 switch21 m R1 z ratio
        (ctmcStructuredSurgePrice mI zI switch12 switch21) σI σJ) :
    GN21SurgeLemma9AcceptAllAggregateRewardRateData
      μI μJ arrivalI arrivalJ switch12 switch21 m R1 z ratio mI zI
      σI σJ where
  current_mass_pos := D.current_mass_pos
  bounds := D.bounds
  z_eq := D.z_eq
  m_sub_R1_pos := D.m_sub_R1_pos
  R1_nonneg := D.R1_nonneg
  fixed_reward_rate :=
    gn21MeasuredStateRewardRate_eq_of_scaled_earning
      μI arrivalI R1 (ctmcStructuredSurgePrice mI zI switch12 switch21)
      σI hfixed_mass hfixed_arrival_mass hfixed_time D.fixed_reward_rate

/--
Lemma 10 reward-rate data are invariant under a null change to the fixed surge
policy.  This is the a.e. bridge needed by the sequential Theorem 3 route:
after proving the surge state is accept-all a.e., non-surge Lemma 10 data
stated with exact accept-all can be reused at the original optimal policy.
-/
theorem GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.congr_fixed_policy_ae
    {μI μJ : Measure TripLength}
    {arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ : ℝ}
    {σI σJ τJ : TripPolicy}
    (hae : policyAlmostEverywhereEq μJ σJ τJ)
    (D :
      GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
        μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ
        σI σJ) :
    GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
      μI μJ arrivalI arrivalJ switch12 switch21 R2 z ratio mJ zJ
      σI τJ where
  current_mass_pos := D.current_mass_pos
  bounds := by
    have hT := gn21ScaledStateTime_congr_policy_ae μJ arrivalJ hae
    have hQ :=
      gn21ExitWeightIntegral_congr_policy_ae μJ arrivalJ switch21
        switch12 hae
    simpa [hT, hQ] using D.bounds
  z_eq := D.z_eq
  R2_pos := D.R2_pos
  fixed_reward_rate := by
    have hreward :=
      gn21MeasuredStateRewardRate_congr_policy_ae μJ arrivalJ
        (ctmcStructuredSurgePrice mJ zJ switch21 switch12) hae
    rw [← hreward]
    exact D.fixed_reward_rate

/--
Lemma 9 reward-rate data are invariant under a null change to the fixed
non-surge policy.
-/
theorem GN21SurgeLemma9AcceptAllAggregateRewardRateData.congr_fixed_policy_ae
    {μI μJ : Measure TripLength}
    {arrivalI arrivalJ switch12 switch21 m R1 z ratio mI zI : ℝ}
    {σI τI σJ : TripPolicy}
    (hae : policyAlmostEverywhereEq μI σI τI)
    (D :
      GN21SurgeLemma9AcceptAllAggregateRewardRateData
        μI μJ arrivalI arrivalJ switch12 switch21 m R1 z ratio mI zI
        σI σJ) :
    GN21SurgeLemma9AcceptAllAggregateRewardRateData
      μI μJ arrivalI arrivalJ switch12 switch21 m R1 z ratio mI zI
      τI σJ where
  current_mass_pos := D.current_mass_pos
  bounds := by
    have hT := gn21ScaledStateTime_congr_policy_ae μI arrivalI hae
    have hQ :=
      gn21ExitWeightIntegral_congr_policy_ae μI arrivalI switch12
        switch21 hae
    simpa [hT, hQ] using D.bounds
  z_eq := D.z_eq
  m_sub_R1_pos := D.m_sub_R1_pos
  R1_nonneg := D.R1_nonneg
  fixed_reward_rate := by
    have hreward :=
      gn21MeasuredStateRewardRate_congr_policy_ae μI arrivalI
        (ctmcStructuredSurgePrice mI zI switch12 switch21) hae
    rw [← hreward]
    exact D.fixed_reward_rate

/--
Local surge-state positive-response step from Lemma 9 reward-rate data.  The
fixed non-surge reward rate is a local current-policy rate `Rcurrent`, matching
the paper's local Lemma 9 notation rather than the global Theorem 3 target
rate.
-/
theorem acceptAllAlmostEverywhere_surge_of_structured_reward_rate_positive_response
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R2 Rcurrent ratioN ratioS switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hacceptAll_mass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy)
    (htime2_acceptAll_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq2_acceptAll_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (DN :
      GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        R2 (z 0) ratioN (m 1) (z 1) (ρ 0) acceptAllPolicy)
    (DS :
      GN21SurgeLemma9AcceptAllAggregateRewardRateData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (m 1) Rcurrent (z 1) ratioS (m 0) (z 0) (ρ 0) (ρ 1)) :
    acceptAllAlmostEverywhere (μ 1) (ρ 1) := by
  have DSsrc :
      GN21SurgeLemma9AcceptAllAggregateSourceData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (m 1) Rcurrent (z 1) ratioS
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ρ 0) (ρ 1) := by
    have D0 :=
      GN21SurgeLemma9AcceptAllAggregateSourceData.of_reward_rate
        (ne_of_gt DN.current_mass_pos)
        (mul_ne_zero (ne_of_gt harrival1_pos)
          (ne_of_gt DN.current_mass_pos))
        (ne_of_gt
          (gn21ScaledStateTime_pos_of_nonneg
            (μ 0) (arrival 0) (ρ 0) (le_of_lt harrival1_pos)
            (hρ.1 0).2 (hρ.1 0).1))
        DS
    simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using D0
  let DP :
      GN21SurgeLemma9AcceptAllAggregatePrimitiveData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (m 1) Rcurrent (z 1) ratioS
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ρ 0) (ρ 1) :=
    GN21SurgeLemma9AcceptAllAggregatePrimitiveData.of_source
      (hρ.1 0).1 (hρ.1 0).2 (hρ.1 1).1 (hρ.1 1).2
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime2_acceptAll_integrable hq2_acceptAll_integrable DSsrc
  let DA := GN21SurgeLemma9AcceptAllAggregateData.of_primitive DP
  let response :=
    gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
      (ρ 0) (ρ 1)
  have hresponse_measurable : Measurable response := by
    simpa [response] using
      measurable_gn21MeasuredRightMarginalResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1)
        ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
          1).measurable)
  have hresponse_integrable :
      IntegrableOn response acceptAllPolicy (μ 1) := by
    have hw_acceptAll :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy (μ 1) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
          switch21 switch12 acceptAllPolicy
          htime2_acceptAll_integrable hq2_acceptAll_integrable
    simpa [response] using
      integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1) acceptAllPolicy hq2_acceptAll_integrable
        hw_acceptAll htime2_acceptAll_integrable
  have hTi_pos :
      0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival1_pos) (hρ.1 0).2 (hρ.1 0).1
  have hTj_pos :
      0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival2_pos) (hρ.1 1).2 (hρ.1 1).1
  let Rj :=
    gn21MeasuredStateRewardRate (μ 1) (arrival 1)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1)
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 1) =
        Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate
      (μ 1) (arrival 1) Rj
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1)
      (ne_of_gt DS.current_mass_pos)
      (ne_of_gt (mul_pos harrival2_pos DS.current_mass_pos))
      (ne_of_gt hTj_pos) rfl
  have hbase :
      Lemma5PositiveResponsePolicyFormData
        (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1) Rcurrent Rj) .positive :=
    Lemma5PositiveResponsePolicyFormData.positive
      (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1) Rcurrent Rj)
      (by
        have hpos :=
          gn21MeasuredRightLemma6ResponseAtCurrent_pos_of_lemma9_current_bounds
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (m 1) Rcurrent (z 1) ratioS Rj
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) (ρ 1) DS.bounds DS.z_eq DS.m_sub_R1_pos
            DS.R1_nonneg DA.fixed_time_nonneg DA.fixed_exit_pos
            DA.switch_pos DA.switch_sum_pos DA.switch_lt_current_exit
            DA.current_gap_nonneg DP.time_integrable_current
            DP.q_integrable_current hTi_pos hTj_pos DSsrc.fixed_reward_rate
            (by
              simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
                using hWj)
        intro τ hτ
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
          using hpos τ hτ)
  have hpositive_form :
      lemma5PolicyForm .positive (lemma5PositiveResponsePolicy response) := by
    have hscaled :
        Lemma5PositiveResponsePolicyFormData response .positive := by
      simpa [response] using
        gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1) Rcurrent Rj hbase DA.fixed_exit_pos hTi_pos
          hTj_pos DA.denominator_pos DSsrc.fixed_reward_rate hWj
    exact hscaled.policy_form
  have hcandidate :
      lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
        lemma5MarginalSetReward (μ 1) response (ρ 1) := by
    have hw_acceptAll :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy (μ 1) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
          switch21 switch12 acceptAllPolicy
          htime2_acceptAll_integrable hq2_acceptAll_integrable
    have hw_current :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 1) (μ 1) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
          switch21 switch12 (ρ 1) DP.time_integrable_current
          DP.q_integrable_current
    have hQ_acceptAll_pos :
        0 <
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy :=
      gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1)
        switch21 switch12 acceptAllPolicy (le_of_lt harrival2_pos)
        hswitch21_pos (by linarith [hswitch12_pos, hswitch21_pos])
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have hT_acceptAll_pos :
        0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
        acceptAllPolicy (le_of_lt harrival2_pos)
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have hden_acceptAll_pos :
        0 <
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
              acceptAllPolicy *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
      gn21AggregateDenominator_pos_of_pos
        (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
          (ρ 0))
        (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
          acceptAllPolicy)
        (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
        (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
        DA.fixed_exit_pos hQ_acceptAll_pos hTi_pos hT_acceptAll_pos
    have hcurrent_nondegenerate :
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (ρ 1) :=
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) (ρ 1) DN.current_mass_pos DS.current_mass_pos
        harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        (hρ.1 0).2 (hρ.1 1).2 (hρ.1 0).1 (hρ.1 1).1
    have hsurge_acceptAll_nondegenerate :
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) acceptAllPolicy :=
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) acceptAllPolicy DN.current_mass_pos hacceptAll_mass2_pos
        harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        (hρ.1 0).2 measurableSet_acceptAllPolicy (hρ.1 0).1
        (fun _ hτ => hτ)
    simpa [response] using
      lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_one
        μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) hρ
        harrival2_pos hcurrent_nondegenerate hsurge_acceptAll_nondegenerate
        DA.denominator_pos hden_acceptAll_pos hq2_acceptAll_integrable
        hw_acceptAll htime2_acceptAll_integrable DP.q_integrable_current
        hw_current DP.time_integrable_current
  have hpositive_eq :
      lemma5PositiveResponsePolicy response = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response)
      hpositive_form
  exact
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 1) response (ρ 1) hresponse_measurable hresponse_integrable
      (hρ.1 1).2 (hρ.1 1).1 hpositive_form
      (by simpa [hpositive_eq] using hcandidate)

/--
Local non-surge positive-response step from Lemma 10 reward-rate data.  The
fixed surge policy can be the original optimal policy; in the sequential paper
route this data is obtained from exact accept-all using the a.e. congruence
lemma after the surge step has been proved.
-/
theorem acceptAllAlmostEverywhere_nonsurge_of_structured_reward_rate_positive_response
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R2 Rcurrent ratioN ratioS switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hm0 : m 0 = R2)
    (hacceptAll_mass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy)
    (htime1_acceptAll_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq1_acceptAll_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (DN :
      GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        R2 (z 0) ratioN (m 1) (z 1) (ρ 0) (ρ 1))
    (DS :
      GN21SurgeLemma9AcceptAllAggregateRewardRateData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (m 1) Rcurrent (z 1) ratioS (m 0) (z 0) (ρ 0) (ρ 1)) :
    acceptAllAlmostEverywhere (μ 0) (ρ 0) := by
  have DNsrc :
      GN21NonsurgeLemma10AcceptAllAggregateSourceData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        R2 (z 0) ratioN
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1) := by
    have D0 :=
      GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_reward_rate
        (ne_of_gt DS.current_mass_pos)
        (mul_ne_zero (ne_of_gt harrival2_pos)
          (ne_of_gt DS.current_mass_pos))
        (ne_of_gt
          (gn21ScaledStateTime_pos_of_nonneg
            (μ 1) (arrival 1) (ρ 1) (le_of_lt harrival2_pos)
            (hρ.1 1).2 (hρ.1 1).1))
        DN
    simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using D0
  let DP :
      GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        R2 (z 0) ratioN
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1) :=
    GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData.of_source
      (hρ.1 0).1 (hρ.1 0).2 (hρ.1 1).1 (hρ.1 1).2
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_acceptAll_integrable hq1_acceptAll_integrable DNsrc
  let DA := GN21NonsurgeLemma10AcceptAllAggregateData.of_primitive DP
  let response :=
    gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
      (ρ 0) (ρ 1)
  have hresponse_measurable : Measurable response := by
    simpa [response] using
      measurable_gn21MeasuredLeftMarginalResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1)
        ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
          0).measurable)
  have hresponse_integrable :
      IntegrableOn response acceptAllPolicy (μ 0) := by
    have hw_acceptAll :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy (μ 0) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
          switch12 switch21 acceptAllPolicy
          htime1_acceptAll_integrable hq1_acceptAll_integrable
    simpa [response] using
      integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1) acceptAllPolicy hq1_acceptAll_integrable
        hw_acceptAll htime1_acceptAll_integrable
  have hTi_pos :
      0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival1_pos) (hρ.1 0).2 (hρ.1 0).1
  have hTj_pos :
      0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival2_pos) (hρ.1 1).2 (hρ.1 1).1
  let Ri :=
    gn21MeasuredStateRewardRate (μ 0) (arrival 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0)
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ρ 0) =
        Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate
      (μ 0) (arrival 0) Ri
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0)
      (ne_of_gt DN.current_mass_pos)
      (ne_of_gt (mul_pos harrival1_pos DN.current_mass_pos))
      (ne_of_gt hTi_pos) rfl
  have hbase :
      Lemma5PositiveResponsePolicyFormData
        (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ρ 0) (ρ 1) Ri R2) .positive :=
    Lemma5PositiveResponsePolicyFormData.positive
      (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ρ 0) (ρ 1) Ri R2)
      (by
        have hpos :=
          gn21MeasuredLeftLemma6ResponseAtCurrent_pos_of_lemma10_current_bounds
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            R2 (z 0) ratioN Ri
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) (ρ 1) DN.bounds DN.z_eq DN.R2_pos DA.fixed_exit_pos
            DA.switch_pos DA.switch_sum_pos DA.switch_lt_current_exit
            DA.current_gap_nonneg DA.lower_numerator_pos
            DP.time_integrable_current DP.q_integrable_current hTi_pos
            hTj_pos
            (by
              simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
                hm0]
                using hWi)
            DNsrc.fixed_reward_rate
        intro τ hτ
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb, hm0]
          using hpos τ hτ)
  have hpositive_form :
      lemma5PolicyForm .positive (lemma5PositiveResponsePolicy response) := by
    have hscaled :
        Lemma5PositiveResponsePolicyFormData response .positive := by
      simpa [response] using
        gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1) Ri R2 hbase DA.fixed_exit_pos hTi_pos hTj_pos
          DA.denominator_pos hWi DNsrc.fixed_reward_rate
    exact hscaled.policy_form
  have hcandidate :
      lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
        lemma5MarginalSetReward (μ 0) response (ρ 0) := by
    have hw_acceptAll :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy (μ 0) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
          switch12 switch21 acceptAllPolicy
          htime1_acceptAll_integrable hq1_acceptAll_integrable
    have hw_current :
        IntegrableOn
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ρ 0) (μ 0) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
        ctmcStructuredSurgePrice] using
        integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
          switch12 switch21 (ρ 0) DP.time_integrable_current
          DP.q_integrable_current
    have hsum12 : 0 < switch12 + switch21 := by
      linarith [hswitch12_pos, hswitch21_pos]
    have hQ_acceptAll_pos :
        0 <
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy :=
      gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0)
        switch12 switch21 acceptAllPolicy (le_of_lt harrival1_pos)
        hswitch12_pos hsum12 measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
    have hT_acceptAll_pos :
        0 < gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0)
        acceptAllPolicy (le_of_lt harrival1_pos)
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have hden_acceptAll_pos :
        0 <
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              acceptAllPolicy *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
              (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
      gn21AggregateDenominator_pos_of_pos
        (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
          acceptAllPolicy)
        (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
          (ρ 1))
        (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
        (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
        hQ_acceptAll_pos DA.fixed_exit_pos hT_acceptAll_pos hTj_pos
    have hcurrent_nondegenerate :
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (ρ 1) :=
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) (ρ 1) DN.current_mass_pos DS.current_mass_pos
        harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        (hρ.1 0).2 (hρ.1 1).2 (hρ.1 0).1 (hρ.1 1).1
    have hnonsurge_acceptAll_nondegenerate :
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 acceptAllPolicy (ρ 1) :=
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        acceptAllPolicy (ρ 1) hacceptAll_mass1_pos DS.current_mass_pos
        harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        measurableSet_acceptAllPolicy (hρ.1 1).2 (fun _ hτ => hτ)
        (hρ.1 1).1
    simpa [response] using
      lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero
        μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) hρ
        harrival1_pos hcurrent_nondegenerate
        hnonsurge_acceptAll_nondegenerate DA.denominator_pos
        hden_acceptAll_pos hq1_acceptAll_integrable hw_acceptAll
        htime1_acceptAll_integrable DP.q_integrable_current hw_current
        DP.time_integrable_current
  have hpositive_eq :
      lemma5PositiveResponsePolicy response = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response)
      hpositive_form
  exact
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 0) response (ρ 0) hresponse_measurable hresponse_integrable
      (hρ.1 0).2 (hρ.1 0).1 hpositive_form
      (by simpa [hpositive_eq] using hcandidate)

/--
Sequential optimal-policy reward-rate data for the positive-response
uniqueness route.  The surge state is handled first at the current optimal
policy; non-surge Lemma 10 is then required only with the surge state fixed at
accept-all, matching the paper proof order.
-/
structure Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  accept_all_optimal :
    dynamicMeasurableOptimal
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
      acceptAllDynamicPolicy
  m0_eq : m 0 = R2
  arrival1_pos : 0 < arrival 0
  arrival2_pos : 0 < arrival 1
  switch12_pos : 0 < switch12
  switch21_pos : 0 < switch21
  acceptAll_mass_pos :
    ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy
  time1_acceptAll_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  time2_acceptAll_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  q1_acceptAll_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  q2_acceptAll_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  nonsurge_after_surge_data :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
        ∃ ratio : ℝ,
          GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            R2 (z 0) ratio (m 1) (z 1) (ρ 0) acceptAllPolicy
  surge_data :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
        ∃ R1_current ratio : ℝ,
          GN21SurgeLemma9AcceptAllAggregateRewardRateData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (m 1) R1_current (z 1) ratio (m 0) (z 0) (ρ 0) (ρ 1)

/--
Existing feasible sequential source current-bounds data instantiate the
reward-rate positive-response certificate for measurable optima.  This bridge
keeps the public source obligations in the older Appendix-D scaled form while
letting the a.e.-uniqueness proof use the paper's local reward-rate notation.
-/
def Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate.of_feasible_sequential_source
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ)
    (accept_all_optimal :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy)
    (C :
      Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsSourceCertificate
        μ arrival R2 switch12 switch21 m z) :
    Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
      μ arrival R1 R2 switch12 switch21 m z where
  accept_all_optimal := accept_all_optimal
  m0_eq := C.m0_eq
  arrival1_pos := C.arrival1_pos
  arrival2_pos := C.arrival2_pos
  switch12_pos := C.switch12_pos
  switch21_pos := C.switch21_pos
  acceptAll_mass_pos := C.acceptAll_mass_pos
  time1_acceptAll_integrable := C.time1_acceptAll_integrable
  time2_acceptAll_integrable := C.time2_acceptAll_integrable
  q1_acceptAll_integrable := C.q1_acceptAll_integrable
  q2_acceptAll_integrable := C.q2_acceptAll_integrable
  nonsurge_after_surge_data := by
    intro ρ hρ
    rcases C.nonsurge_after_surge_data ρ hρ.1 with ⟨ratio, Dsrc⟩
    have hmassJ :
        singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
      ne_of_gt (C.acceptAll_mass_pos 1)
    have harrivalMassJ :
        arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
      mul_ne_zero (ne_of_gt C.arrival2_pos) hmassJ
    have htimeJ_pos :
        0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
        acceptAllPolicy (le_of_lt C.arrival2_pos)
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have Dsrc_structured :
        GN21NonsurgeLemma10AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          R2 (z 0) ratio
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
          (ρ 0) acceptAllPolicy := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using Dsrc
    exact
      ⟨ratio,
        GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_source_structured
          hmassJ harrivalMassJ (ne_of_gt htimeJ_pos) Dsrc_structured⟩
  surge_data := by
    intro ρ hρ
    rcases C.nonsurge_after_surge_data ρ hρ.1 with ⟨_ratioN, DNsrc⟩
    rcases C.surge_data ρ hρ.1 with ⟨R1_current, ratioS, DSsrc⟩
    have hmassI : singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      ne_of_gt DNsrc.current_mass_pos
    have harrivalMassI :
        arrival 0 * singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      mul_ne_zero (ne_of_gt C.arrival1_pos) hmassI
    have htimeI_pos :
        0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
        (le_of_lt C.arrival1_pos) (hρ.1 0).2 (hρ.1 0).1
    have DSsrc_structured :
        GN21SurgeLemma9AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratioS
          (ctmcStructuredSurgePrice (m 0) (z 0) switch12 switch21)
          (ρ 0) (ρ 1) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using DSsrc
    exact
      ⟨R1_current, ratioS,
        GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_source_structured
          hmassI harrivalMassI (ne_of_gt htimeI_pos) DSsrc_structured⟩

/--
Optimal-policy sequential source data in the Appendix-D scaled form.  This is
the paper-faithful boundary for a.e. uniqueness: weak IC may still use
feasible-policy data, but Lemma 9/10 positive-response data are needed only at
measurable optima.  The surge step is stated first at the current non-surge
policy; the non-surge step is stated after the surge state is fixed at
accept-all.
-/
structure Theorem4MeasuredAggregateStructuredSequentialOptimalCurrentBoundsSourceCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  accept_all_optimal :
    dynamicMeasurableOptimal
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
      acceptAllDynamicPolicy
  m0_eq : m 0 = R2
  arrival1_pos : 0 < arrival 0
  arrival2_pos : 0 < arrival 1
  switch12_pos : 0 < switch12
  switch21_pos : 0 < switch21
  acceptAll_mass_pos :
    ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy
  time1_acceptAll_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  time2_acceptAll_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  q1_acceptAll_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  q2_acceptAll_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  nonsurge_after_surge_data :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
        ∃ ratio : ℝ,
          GN21NonsurgeLemma10AcceptAllAggregateSourceData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            R2 (z 0) ratio
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) acceptAllPolicy
  surge_data :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
        ∃ R1_current ratio : ℝ,
          GN21SurgeLemma9AcceptAllAggregateSourceData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (m 1) R1_current (z 1) ratio
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) (ρ 1)

/--
Convert optimal-only sequential Appendix-D source data to the local
reward-rate form consumed by the source-ordered positive-response proof.
-/
def Theorem4MeasuredAggregateStructuredSequentialOptimalCurrentBoundsSourceCertificate.to_reward_rate_positive_response
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (C :
      Theorem4MeasuredAggregateStructuredSequentialOptimalCurrentBoundsSourceCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
      μ arrival R1 R2 switch12 switch21 m z where
  accept_all_optimal := C.accept_all_optimal
  m0_eq := C.m0_eq
  arrival1_pos := C.arrival1_pos
  arrival2_pos := C.arrival2_pos
  switch12_pos := C.switch12_pos
  switch21_pos := C.switch21_pos
  acceptAll_mass_pos := C.acceptAll_mass_pos
  time1_acceptAll_integrable := C.time1_acceptAll_integrable
  time2_acceptAll_integrable := C.time2_acceptAll_integrable
  q1_acceptAll_integrable := C.q1_acceptAll_integrable
  q2_acceptAll_integrable := C.q2_acceptAll_integrable
  nonsurge_after_surge_data := by
    intro ρ hρ
    rcases C.nonsurge_after_surge_data ρ hρ with ⟨ratio, Dsrc⟩
    have hmassJ :
        singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
      ne_of_gt (C.acceptAll_mass_pos 1)
    have harrivalMassJ :
        arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
      mul_ne_zero (ne_of_gt C.arrival2_pos) hmassJ
    have htimeJ_pos :
        0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
        acceptAllPolicy (le_of_lt C.arrival2_pos)
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have Dsrc_structured :
        GN21NonsurgeLemma10AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          R2 (z 0) ratio
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
          (ρ 0) acceptAllPolicy := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using Dsrc
    exact
      ⟨ratio,
        GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_source_structured
          hmassJ harrivalMassJ (ne_of_gt htimeJ_pos) Dsrc_structured⟩
  surge_data := by
    intro ρ hρ
    rcases C.nonsurge_after_surge_data ρ hρ with ⟨_ratioN, DNsrc⟩
    rcases C.surge_data ρ hρ with ⟨R1_current, ratioS, DSsrc⟩
    have hmassI : singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      ne_of_gt DNsrc.current_mass_pos
    have harrivalMassI :
        arrival 0 * singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      mul_ne_zero (ne_of_gt C.arrival1_pos) hmassI
    have htimeI_pos :
        0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
        (le_of_lt C.arrival1_pos) (hρ.1 0).2 (hρ.1 0).1
    have DSsrc_structured :
        GN21SurgeLemma9AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratioS
          (ctmcStructuredSurgePrice (m 0) (z 0) switch12 switch21)
          (ρ 0) (ρ 1) := by
      simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb] using DSsrc
    exact
      ⟨R1_current, ratioS,
        GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_source_structured
          hmassI harrivalMassI (ne_of_gt htimeI_pos) DSsrc_structured⟩

/--
Sequential optimal reward-rate positive-response data imply the Theorem 4
a.e. accept-all conclusion directly.  This follows the paper order: Lemma 9
first proves the surge state accepts all a.e.; Lemma 10 is then transported
from exact accept-all surge to the original optimal policy by null-set
congruence and proves the non-surge state accepts all a.e.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_sequential_optimal_reward_rate_positive_response
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ)
    (C :
      Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  rcases C.nonsurge_after_surge_data ρ hρ with ⟨ratioN, DN⟩
  rcases C.surge_data ρ hρ with ⟨R1_current, ratioS, DS⟩
  have hsurge :
      acceptAllAlmostEverywhere (μ 1) (ρ 1) :=
    acceptAllAlmostEverywhere_surge_of_structured_reward_rate_positive_response
      (μ := μ) (arrival := arrival) (m := m) (z := z)
      (R2 := R2) (Rcurrent := R1_current) (ratioN := ratioN)
      (ratioS := ratioS) (switch12 := switch12) (switch21 := switch21)
      hρ C.arrival1_pos C.arrival2_pos C.switch12_pos C.switch21_pos
      (C.acceptAll_mass_pos 1) C.time2_acceptAll_integrable
      C.q2_acceptAll_integrable DN DS
  have hae_surge :
      policyAlmostEverywhereEq (μ 1) acceptAllPolicy (ρ 1) :=
    (policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
      (μ 1) (hρ.1 1).1 hsurge).symm
  have DN_current :
      GN21NonsurgeLemma10AcceptAllAggregateRewardRateData
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        R2 (z 0) ratioN (m 1) (z 1) (ρ 0) (ρ 1) :=
    GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.congr_fixed_policy_ae
      hae_surge DN
  have hnonsurge :
      acceptAllAlmostEverywhere (μ 0) (ρ 0) :=
    acceptAllAlmostEverywhere_nonsurge_of_structured_reward_rate_positive_response
      (μ := μ) (arrival := arrival) (m := m) (z := z)
      (R2 := R2) (Rcurrent := R1_current) (ratioN := ratioN)
      (ratioS := ratioS) (switch12 := switch12) (switch21 := switch21)
      hρ C.arrival1_pos C.arrival2_pos C.switch12_pos C.switch21_pos
      C.m0_eq (C.acceptAll_mass_pos 0) C.time1_acceptAll_integrable
      C.q1_acceptAll_integrable DN_current DS
  fin_cases i
  · exact hnonsurge
  · exact hsurge

/--
Theorem 3 via weak feasible IC plus the source-ordered sequential
optimal-policy reward-rate positive-response proof.  This is the paper-faithful
route when Lemma 9 supplies a local current non-surge reward rate first and
Lemma 10 is applied only after the surge state is accept-all a.e.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (weak_reward :
      theorem3AcceptAllFeasibleWeakRewardCertificate
        μ arrival R1 R2 switch12 switch21)
    (optimal_sequential_reward_rate :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
          μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  have hmass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy := by
    rw [hmass1_eq_one]
    norm_num
  have hmass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy := by
    rw [hmass2_eq_one]
    norm_num
  have hmeasure1_pos : 0 < μ 0 acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos (μ 0) acceptAllPolicy hmass1_pos
  have hmeasure2_pos : 0 < μ 1 acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos (μ 1) acceptAllPolicy hmass2_pos
  rcases theorem3_acceptAll_ratio_source_scalar_consequences
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      rho R1 R2 hR1_eq hR2_pos hC_lt_rho hrho_lt_one
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable hq1_integrable hmeasure1_pos with
    ⟨_, hR1_pos, hR1_lt_R2⟩
  rcases
      paper_theorem3_measured_structured_measurable_ic_prices_of_feasible_weak_reward
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR1_pos
        hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one harrival1_pos
        harrival2_pos hswitch12_pos hswitch21_pos htime1_integrable
        htime2_integrable hq1_integrable hq2_integrable hmeasure1_pos
        hmeasure2_pos weak_reward with
    ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  have H :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_sequential_optimal_reward_rate_positive_response
      μ arrival R1 R2 switch12 switch21 m z
      (optimal_sequential_reward_rate m z hsigns hparams)
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
    intro ρ hρ
    have hρ' :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) ρ := by
      simpa [gn21MeasuredCTMCStructuredDynamicReward] using hρ
    exact H.2 ρ hρ'
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

/--
Theorem 3 from weak feasible IC plus the existing feasible sequential
current-bounds source certificate.  The weak IC certificate derives exact
accept-all optimality; the source certificate supplies the paper-order Lemma
9/10 data that the split module converts to reward-rate form for a.e.
uniqueness.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_feasible_sequential_source_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (weak_reward :
      theorem3AcceptAllFeasibleWeakRewardCertificate
        μ arrival R1 R2 switch12 switch21)
    (feasible_sequential_source :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsSourceCertificate
          μ arrival R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one weak_reward
    (by
      intro m z hsigns hparams
      have haccept :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            acceptAllDynamicPolicy := by
        have hweak := weak_reward m z hsigns hparams
        have hopt :=
          paper_theorem4_measurable_accept_all_optimal_of_statewise_accept_all_weak_reward
            (gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12
              switch21 m z) hweak
        simpa [gn21MeasuredCTMCStructuredDynamicReward] using hopt
      exact
        Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate.of_feasible_sequential_source
          μ arrival R1 R2 switch12 switch21 m z haccept
          (feasible_sequential_source m z hsigns hparams))

/--
Theorem 3 from weak feasible IC plus optimal-only sequential Appendix-D source
data.  This is the same source-ordered route as the reward-rate theorem, but
the public boundary is the paper's scaled `T,Q,W` data and it is required only
for measurable optima.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_source_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (weak_reward :
      theorem3AcceptAllFeasibleWeakRewardCertificate
        μ arrival R1 R2 switch12 switch21)
    (optimal_sequential_source :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredSequentialOptimalCurrentBoundsSourceCertificate
          μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one weak_reward
    (by
      intro m z hsigns hparams
      exact
        (optimal_sequential_source m z hsigns hparams).to_reward_rate_positive_response)

/--
Source-facing optimal-only sequential surge data after the Lemma 10 accept-all
fixed-surge branch has been constructed from Theorem 3 parameter data.  Unlike
the older feasible sequential source wrapper, this package asks for the
non-surge current positive-mass fact and Lemma 9 surge source data only at
measurable optima.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeSourceDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  hR1_eq : R1 = rho * R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1
  weak_reward :
    theorem3AcceptAllFeasibleWeakRewardCertificate
      μ arrival R1 R2 switch12 switch21
  optimal_nonsurge_current_mass_pos :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          0 < singleStateTripMass (μ 0) (ρ 0)
  surge_source_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateSourceData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) (ρ 1)

/--
Theorem 3 a.e.-uniqueness wrapper for optimal-only sequential surge source
data.  Weak feasible IC is supplied separately; the Lemma 10 accept-all branch
is built from the constructed price parameters, and the remaining Lemma 9 data
are required only for measurable optima.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_source_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 A.hR1_eq A.hR2_pos
    A.hC_lt_rho A.hrho_lt_one A.harrival1_pos A.harrival2_pos
    A.hswitch12_pos A.hswitch21_pos A.htime1_integrable
    A.htime2_integrable A.hq1_integrable A.hq2_integrable
    A.hmass1_eq_one A.hmass2_eq_one A.weak_reward
    (by
      intro m z hnonneg hparams
      let P := Theorem3AcceptAllStructuredParameterData.of_evidence hparams
      exact
        { accept_all_optimal := by
            have hweak := A.weak_reward m z hnonneg hparams
            have hopt :=
              paper_theorem4_measurable_accept_all_optimal_of_statewise_accept_all_weak_reward
                (gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12
                  switch21 m z) hweak
            simpa [gn21MeasuredCTMCStructuredDynamicReward] using hopt
          m0_eq := P.hm0
          arrival1_pos := A.harrival1_pos
          arrival2_pos := A.harrival2_pos
          switch12_pos := A.hswitch12_pos
          switch21_pos := A.hswitch21_pos
          acceptAll_mass_pos := by
            intro i
            fin_cases i
            · simpa [A.hmass1_eq_one]
            · simpa [A.hmass2_eq_one]
          time1_acceptAll_integrable := A.htime1_integrable
          time2_acceptAll_integrable := A.htime2_integrable
          q1_acceptAll_integrable := A.hq1_integrable
          q2_acceptAll_integrable := A.hq2_integrable
          nonsurge_after_surge_data := by
            intro ρ hρ
            have hsum21 : 0 < switch21 + switch12 := by
              linarith [A.hswitch21_pos, A.hswitch12_pos]
            have hfixed_exit_pos :
                0 <
                  gn21ExitWeightIntegral (μ 1) (arrival 1)
                    switch21 switch12 acceptAllPolicy :=
              gn21ExitWeightIntegral_pos_of_switch_pos
                (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
                (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
                measurableSet_acceptAllPolicy (fun _ hτ => hτ)
            have hfixed_time_pos :
                0 <
                  gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
              gn21ScaledStateTime_pos_of_nonneg
                (μ 1) (arrival 1) acceptAllPolicy
                (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
                (fun _ hτ => hτ)
            have hfixed_A_pos :
                0 <
                  gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
                      switch12 +
                    gn21ExitWeightIntegral (μ 1) (arrival 1)
                      switch21 switch12 acceptAllPolicy :=
              add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
                hfixed_exit_pos
            have hfixed_reward_rate :
                gn21ScaledStateEarning (μ 1) (arrival 1)
                    (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                    acceptAllPolicy =
                  R2 * gn21ScaledStateTime (μ 1) (arrival 1)
                    acceptAllPolicy := by
              calc
                gn21ScaledStateEarning (μ 1) (arrival 1)
                    (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                    acceptAllPolicy
                    =
                  m 1 *
                      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
                    z 1 *
                      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                          switch21 switch12 -
                        switch21) := by
                      simpa [ctmcStructuredDynamicSurgePrice,
                        ctmcDynamicSwitchProb, ctmcStructuredSurgePrice,
                        gn21AcceptAllScaledStateTime,
                        gn21AcceptAllExitWeightIntegral] using
                        paper_remark2_structured_scaled_earning_algebra
                          (μ 1) (arrival 1) (m 1) (z 1) switch21 switch12
                          acceptAllPolicy A.htime2_integrable
                          A.hq2_integrable
                _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
                  P.surge_accounting
            exact
              ⟨P.nonsurgeRatio,
                GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening
                  (hρ.1 0).1 (hρ.1 0).2 A.harrival1_pos
                  A.hswitch12_pos A.hswitch21_pos
                  (A.htime1_integrable.mono_set (hρ.1 0).1)
                  (A.hq1_integrable.mono_set (hρ.1 0).1)
                  A.htime1_integrable A.hq1_integrable
                  P.nonsurge_acceptAll_bounds hfixed_A_pos
                  (le_of_lt hfixed_exit_pos)
                  (A.optimal_nonsurge_current_mass_pos
                    m z hnonneg hparams ρ hρ)
                  P.hz0 A.hR2_pos hfixed_reward_rate⟩
          surge_data := A.surge_source_data m z hnonneg hparams } )

/--
Accounting-form optimal-only sequential surge data.  Remark 2 converts the
fixed non-surge accounting equation into the Lemma 9 source fixed-reward
identity.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeAccountingDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) extends
      Theorem3AcceptAllStructuredOptimalSequentialSurgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21 where
  surge_accounting_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateAccountingData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio (m 0) (z 0) (ρ 0) (ρ 1)

/-- Accounting-form optimal-only sequential surge source wrapper. -/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_accounting_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeAccountingDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { A.toTheorem3AcceptAllStructuredOptimalSequentialSurgeSourceDataAssumptions with
      surge_source_data := by
        intro m z hnonneg hparams ρ hρ
        rcases A.surge_accounting_data m z hnonneg hparams ρ hρ with
          ⟨R1_current, ratio, D⟩
        have Dsrc :=
          GN21SurgeLemma9AcceptAllAggregateSourceData.of_structured_accounting
            (A.htime1_integrable.mono_set (hρ.1 0).1)
            (A.hq1_integrable.mono_set (hρ.1 0).1) D
        exact ⟨R1_current, ratio, by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using Dsrc⟩ }

/--
Reward-rate-form optimal-only sequential surge data.  The fixed non-surge
positive mass field is kept optimal-only, matching the source proof's actual
use.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeRewardRateDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) extends
      Theorem3AcceptAllStructuredOptimalSequentialSurgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21 where
  surge_reward_rate_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateRewardRateData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio (m 0) (z 0) (ρ 0) (ρ 1)

/-- Reward-rate-form optimal-only sequential surge source wrapper. -/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_reward_rate_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 A.hR1_eq A.hR2_pos
    A.hC_lt_rho A.hrho_lt_one A.harrival1_pos A.harrival2_pos
    A.hswitch12_pos A.hswitch21_pos A.htime1_integrable
    A.htime2_integrable A.hq1_integrable A.hq2_integrable
    A.hmass1_eq_one A.hmass2_eq_one A.weak_reward
    (by
      intro m z hnonneg hparams
      let P := Theorem3AcceptAllStructuredParameterData.of_evidence hparams
      exact
        { accept_all_optimal := by
            have hweak := A.weak_reward m z hnonneg hparams
            have hopt :=
              paper_theorem4_measurable_accept_all_optimal_of_statewise_accept_all_weak_reward
                (gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12
                  switch21 m z) hweak
            simpa [gn21MeasuredCTMCStructuredDynamicReward] using hopt
          m0_eq := P.hm0
          arrival1_pos := A.harrival1_pos
          arrival2_pos := A.harrival2_pos
          switch12_pos := A.hswitch12_pos
          switch21_pos := A.hswitch21_pos
          acceptAll_mass_pos := by
            intro i
            fin_cases i
            · simpa [A.hmass1_eq_one]
            · simpa [A.hmass2_eq_one]
          time1_acceptAll_integrable := A.htime1_integrable
          time2_acceptAll_integrable := A.htime2_integrable
          q1_acceptAll_integrable := A.hq1_integrable
          q2_acceptAll_integrable := A.hq2_integrable
          nonsurge_after_surge_data := by
            intro ρ hρ
            have hsum21 : 0 < switch21 + switch12 := by
              linarith [A.hswitch21_pos, A.hswitch12_pos]
            have hfixed_exit_pos :
                0 <
                  gn21ExitWeightIntegral (μ 1) (arrival 1)
                    switch21 switch12 acceptAllPolicy :=
              gn21ExitWeightIntegral_pos_of_switch_pos
                (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
                (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
                measurableSet_acceptAllPolicy (fun _ hτ => hτ)
            have hfixed_time_pos :
                0 <
                  gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
              gn21ScaledStateTime_pos_of_nonneg
                (μ 1) (arrival 1) acceptAllPolicy
                (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
                (fun _ hτ => hτ)
            have hfixed_A_pos :
                0 <
                  gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
                      switch12 +
                    gn21ExitWeightIntegral (μ 1) (arrival 1)
                      switch21 switch12 acceptAllPolicy :=
              add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
                hfixed_exit_pos
            have hfixed_mass :
                singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 := by
              rw [A.hmass2_eq_one]
              norm_num
            have hfixed_arrival_mass :
                arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
              mul_ne_zero (ne_of_gt A.harrival2_pos) hfixed_mass
            have hfixed_reward_rate :
                gn21MeasuredStateRewardRate (μ 1) (arrival 1)
                    (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                    acceptAllPolicy =
                  R2 := by
              have hscaled :
                  gn21ScaledStateEarning (μ 1) (arrival 1)
                      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                      acceptAllPolicy =
                    R2 * gn21ScaledStateTime (μ 1) (arrival 1)
                      acceptAllPolicy := by
                calc
                  gn21ScaledStateEarning (μ 1) (arrival 1)
                      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                      acceptAllPolicy
                      =
                    m 1 *
                        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
                      z 1 *
                        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                            switch21 switch12 -
                          switch21) := by
                        simpa [ctmcStructuredDynamicSurgePrice,
                          ctmcDynamicSwitchProb, ctmcStructuredSurgePrice,
                          gn21AcceptAllScaledStateTime,
                          gn21AcceptAllExitWeightIntegral] using
                          paper_remark2_structured_scaled_earning_algebra
                            (μ 1) (arrival 1) (m 1) (z 1) switch21 switch12
                            acceptAllPolicy A.htime2_integrable
                            A.hq2_integrable
                  _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
                    P.surge_accounting
              exact
                gn21MeasuredStateRewardRate_eq_of_scaled_earning
                  (μ 1) (arrival 1) R2
                  (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                  acceptAllPolicy hfixed_mass hfixed_arrival_mass
                  (ne_of_gt hfixed_time_pos) hscaled
            exact
              ⟨P.nonsurgeRatio,
                GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_acceptAll_tightening
                  (hρ.1 0).1 (hρ.1 0).2 A.harrival1_pos
                  A.hswitch12_pos A.hswitch21_pos
                  (A.htime1_integrable.mono_set (hρ.1 0).1)
                  (A.hq1_integrable.mono_set (hρ.1 0).1)
                  A.htime1_integrable A.hq1_integrable
                  P.nonsurge_acceptAll_bounds hfixed_A_pos
                  (le_of_lt hfixed_exit_pos)
                  (A.optimal_nonsurge_current_mass_pos
                    m z hnonneg hparams ρ hρ)
                  P.hz0 A.hR2_pos hfixed_mass hfixed_arrival_mass
                  (ne_of_gt hfixed_time_pos) hfixed_reward_rate⟩
          surge_data := A.surge_reward_rate_data m z hnonneg hparams } )

/--
Optimal-only sequential surge data with the zero-mass boundary made explicit.
This is the honest source-domain replacement for assuming positive non-surge
current mass at every full measurable optimum: Lean derives that mass fact
from a strict-dominance certificate ruling out feasible zero-mass optima.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  hR1_eq : R1 = rho * R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1
  weak_reward :
    theorem3AcceptAllFeasibleWeakRewardCertificate
      μ arrival R1 R2 switch12 switch21
  zero_mass_strict_dominance :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        DynamicZeroMassStrictDominanceCertificate μ
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
  surge_source_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateSourceData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) (ρ 1)

/--
The zero-mass bridge supplies the positive non-surge current mass needed by
the existing optimal-only sequential surge Theorem 3 wrapper.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_zero_mass_bridge_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { hR1_eq := A.hR1_eq
      hR2_pos := A.hR2_pos
      hC_lt_rho := A.hC_lt_rho
      hrho_lt_one := A.hrho_lt_one
      harrival1_pos := A.harrival1_pos
      harrival2_pos := A.harrival2_pos
      hswitch12_pos := A.hswitch12_pos
      hswitch21_pos := A.hswitch21_pos
      htime1_integrable := A.htime1_integrable
      htime2_integrable := A.htime2_integrable
      hq1_integrable := A.hq1_integrable
      hq2_integrable := A.hq2_integrable
      hmass1_eq_one := A.hmass1_eq_one
      hmass2_eq_one := A.hmass2_eq_one
      weak_reward := A.weak_reward
      optimal_nonsurge_current_mass_pos := by
        intro m z hnonneg hparams ρ hρ
        exact
          (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
            (A.zero_mass_strict_dominance m z hnonneg hparams) hρ).1.2 0
      surge_source_data := A.surge_source_data }

/--
Accounting-form optimal-only sequential surge data with the zero-mass bridge
instead of an assumed positive non-surge current-mass field.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeAccountingDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) extends
      Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21 where
  surge_accounting_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateAccountingData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio (m 0) (z 0) (ρ 0) (ρ 1)

/-- Accounting-form zero-mass-bridge wrapper for the optimal sequential surge route. -/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_accounting_data_zero_mass_bridge_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeAccountingDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_zero_mass_bridge_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { A.toTheorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions with
      surge_source_data := by
        intro m z hnonneg hparams ρ hρ
        rcases A.surge_accounting_data m z hnonneg hparams ρ hρ with
          ⟨R1_current, ratio, D⟩
        have Dsrc :=
          GN21SurgeLemma9AcceptAllAggregateSourceData.of_structured_accounting
            (A.htime1_integrable.mono_set (hρ.1 0).1)
            (A.hq1_integrable.mono_set (hρ.1 0).1) D
        exact ⟨R1_current, ratio, by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using Dsrc⟩ }

/--
Reward-rate-form optimal-only sequential surge data with the zero-mass bridge
instead of an assumed positive non-surge current-mass field.
-/
structure Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeRewardRateDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) extends
      Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21 where
  surge_reward_rate_data :
    ∀ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        theorem3AcceptAllStructuredParameterEvidence
          μ arrival R1 R2 switch12 switch21 m z →
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          ∃ R1_current ratio : ℝ,
            GN21SurgeLemma9AcceptAllAggregateRewardRateData
              (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
              (m 1) R1_current (z 1) ratio (m 0) (z 0) (ρ 0) (ρ 1)

/-- Reward-rate-form zero-mass-bridge wrapper for the optimal sequential surge route. -/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_reward_rate_data_zero_mass_bridge_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_optimal_sequential_surge_source_data_zero_mass_bridge_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { A.toTheorem3AcceptAllStructuredOptimalSequentialSurgeZeroMassBridgeSourceDataAssumptions with
      surge_source_data := by
        intro m z hnonneg hparams ρ hρ
        rcases A.surge_reward_rate_data m z hnonneg hparams ρ hρ with
          ⟨R1_current, ratio, D⟩
        have hmassI :
            0 < singleStateTripMass (μ 0) (ρ 0) :=
          (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
            (A.zero_mass_strict_dominance m z hnonneg hparams) hρ).1.2 0
        have harrivalMassI :
            arrival 0 * singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
          mul_ne_zero (ne_of_gt A.harrival1_pos) (ne_of_gt hmassI)
        have htimeI_pos :
            0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
          gn21ScaledStateTime_pos_of_nonneg
            (μ 0) (arrival 0) (ρ 0) (le_of_lt A.harrival1_pos)
            (hρ.1 0).2 (hρ.1 0).1
        have Dsrc :=
          GN21SurgeLemma9AcceptAllAggregateSourceData.of_reward_rate
            (ne_of_gt hmassI) harrivalMassI (ne_of_gt htimeI_pos) D
        exact ⟨R1_current, ratio, by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using Dsrc⟩ }

/--
Source-facing feasible sequential current-bounds data prove the full Theorem 3
measurable IC plus a.e.-uniqueness conclusion.  This upgrades the older
source-data IC wrapper by reusing the same sequential Lemma 9/10 data for the
positive-response a.e. proof.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialCurrentBoundsSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  have hseqWeak :
      theorem3AcceptAllFeasibleSequentialWeakRewardCertificate
        μ arrival R1 R2 switch12 switch21 :=
    theorem3AcceptAllFeasibleSequentialWeakRewardCertificate_of_structured_feasible_sequential_current_bounds_source
      μ arrival R1 R2 switch12 switch21
      A.feasible_sequential_current_bounds_source
  rcases
      paper_theorem3_measured_structured_measurable_ic_prices_of_feasible_sequential_weak_reward
        μ arrival rho R1 R2 switch12 switch21 A.hR1_eq A.hR1_pos
        A.hR1_lt_R2 A.hR2_pos A.hC_lt_rho A.hrho_lt_one
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
        A.htime1_integrable A.htime2_integrable A.hq1_integrable
        A.hq2_integrable A.hmeasure1_pos A.hmeasure2_pos hseqWeak with
    ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  have haccept :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy := by
    have hopt :=
      paper_theorem4_measurable_accept_all_optimal_of_sequential_accept_all_weak_reward
        (gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12
          switch21 m z)
        (hseqWeak m z hsigns hparams)
    simpa [gn21MeasuredCTMCStructuredDynamicReward] using hopt
  have H :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_sequential_optimal_reward_rate_positive_response
      μ arrival R1 R2 switch12 switch21 m z
      (Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate.of_feasible_sequential_source
        μ arrival R1 R2 switch12 switch21 m z haccept
        (A.feasible_sequential_current_bounds_source m z hsigns hparams))
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
    intro ρ hρ
    have hρ' :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) ρ := by
      simpa [gn21MeasuredCTMCStructuredDynamicReward] using hρ
    exact H.2 ρ hρ'
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

/--
Theorem 3 a.e.-uniqueness wrapper after the Lemma 10 accept-all fixed-surge
branch has been discharged by Theorem 3 parameter data.  The remaining source
field is the policy-dependent Lemma 9 surge data.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_surge_source_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialSurgeSourceDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { hR1_eq := A.hR1_eq
      hR1_pos := A.hR1_pos
      hR1_lt_R2 := A.hR1_lt_R2
      hR2_pos := A.hR2_pos
      hC_lt_rho := A.hC_lt_rho
      hrho_lt_one := A.hrho_lt_one
      harrival1_pos := A.harrival1_pos
      harrival2_pos := A.harrival2_pos
      hswitch12_pos := A.hswitch12_pos
      hswitch21_pos := A.hswitch21_pos
      htime1_integrable := A.htime1_integrable
      htime2_integrable := A.htime2_integrable
      hq1_integrable := A.hq1_integrable
      hq2_integrable := A.hq2_integrable
      hmeasure1_pos :=
        measure_pos_of_singleStateTripMass_pos
          (μ 0) acceptAllPolicy A.hmass1_pos
      hmeasure2_pos :=
        measure_pos_of_singleStateTripMass_pos
          (μ 1) acceptAllPolicy A.hmass2_pos
      feasible_sequential_current_bounds_source := by
        intro m z hnonneg hparams
        let P := Theorem3AcceptAllStructuredParameterData.of_evidence hparams
        exact
          { m0_eq := P.hm0
            arrival1_pos := A.harrival1_pos
            arrival2_pos := A.harrival2_pos
            switch12_pos := A.hswitch12_pos
            switch21_pos := A.hswitch21_pos
            acceptAll_mass_pos := by
              intro i
              fin_cases i
              · exact A.hmass1_pos
              · exact A.hmass2_pos
            time1_acceptAll_integrable := A.htime1_integrable
            time2_acceptAll_integrable := A.htime2_integrable
            q1_acceptAll_integrable := A.hq1_integrable
            q2_acceptAll_integrable := A.hq2_integrable
            nonsurge_after_surge_data := by
              intro ρ hρ
              have hsum21 : 0 < switch21 + switch12 := by
                linarith [A.hswitch21_pos, A.hswitch12_pos]
              have hfixed_exit_pos :
                  0 <
                    gn21ExitWeightIntegral (μ 1) (arrival 1)
                      switch21 switch12 acceptAllPolicy :=
                gn21ExitWeightIntegral_pos_of_switch_pos
                  (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
                  (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
                  measurableSet_acceptAllPolicy (fun _ hτ => hτ)
              have hfixed_time_pos :
                  0 <
                    gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
                gn21ScaledStateTime_pos_of_nonneg
                  (μ 1) (arrival 1) acceptAllPolicy
                  (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
                  (fun _ hτ => hτ)
              have hfixed_A_pos :
                  0 <
                    gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
                        switch12 +
                      gn21ExitWeightIntegral (μ 1) (arrival 1)
                        switch21 switch12 acceptAllPolicy :=
                add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
                  hfixed_exit_pos
              have hfixed_reward_rate :
                  gn21ScaledStateEarning (μ 1) (arrival 1)
                      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                      acceptAllPolicy =
                    R2 * gn21ScaledStateTime (μ 1) (arrival 1)
                      acceptAllPolicy := by
                calc
                  gn21ScaledStateEarning (μ 1) (arrival 1)
                      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                      acceptAllPolicy
                      =
                    m 1 *
                        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
                      z 1 *
                        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                            switch21 switch12 -
                          switch21) := by
                        simpa [ctmcStructuredDynamicSurgePrice,
                          ctmcDynamicSwitchProb, ctmcStructuredSurgePrice,
                          gn21AcceptAllScaledStateTime,
                          gn21AcceptAllExitWeightIntegral] using
                          paper_remark2_structured_scaled_earning_algebra
                            (μ 1) (arrival 1) (m 1) (z 1) switch21 switch12
                            acceptAllPolicy A.htime2_integrable
                            A.hq2_integrable
                  _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
                    P.surge_accounting
              exact
                ⟨P.nonsurgeRatio,
                  GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening
                    (hρ 0).1 (hρ 0).2 A.harrival1_pos A.hswitch12_pos
                    A.hswitch21_pos
                    (A.htime1_integrable.mono_set (hρ 0).1)
                    (A.hq1_integrable.mono_set (hρ 0).1)
                    A.htime1_integrable A.hq1_integrable
                    P.nonsurge_acceptAll_bounds hfixed_A_pos
                    (le_of_lt hfixed_exit_pos)
                    (A.nonsurge_current_mass_pos m z hnonneg hparams ρ hρ)
                    P.hz0 A.hR2_pos hfixed_reward_rate⟩
            surge_data := A.surge_source_data m z hnonneg hparams } }

/--
Accounting-form Theorem 3 a.e.-uniqueness wrapper for the sequential surge
source route.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_surge_accounting_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialSurgeAccountingDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_surge_source_data_assumptions
    μ arrival rho R1 R2 switch12 switch21
    { hR1_eq := A.hR1_eq
      hR1_pos := A.hR1_pos
      hR1_lt_R2 := A.hR1_lt_R2
      hR2_pos := A.hR2_pos
      hC_lt_rho := A.hC_lt_rho
      hrho_lt_one := A.hrho_lt_one
      harrival1_pos := A.harrival1_pos
      harrival2_pos := A.harrival2_pos
      hswitch12_pos := A.hswitch12_pos
      hswitch21_pos := A.hswitch21_pos
      htime1_integrable := A.htime1_integrable
      htime2_integrable := A.htime2_integrable
      hq1_integrable := A.hq1_integrable
      hq2_integrable := A.hq2_integrable
      hmass1_pos := A.hmass1_pos
      hmass2_pos := A.hmass2_pos
      nonsurge_current_mass_pos := A.nonsurge_current_mass_pos
      surge_source_data := by
        intro m z hnonneg hparams ρ hρ
        rcases A.surge_accounting_data m z hnonneg hparams ρ hρ with
          ⟨R1_current, ratio, D⟩
        have Dsrc :=
          GN21SurgeLemma9AcceptAllAggregateSourceData.of_structured_accounting
            (A.htime1_integrable.mono_set (hρ 0).1)
            (A.hq1_integrable.mono_set (hρ 0).1) D
        exact ⟨R1_current, ratio, by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using Dsrc⟩ }

/--
Constructor for the source-ordered Lemma 9 then Lemma 10 a.e.-uniqueness
certificate when the feasible sequential surge package is already stated in
measured reward-rate form.
-/
def Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate.of_feasible_sequential_surge_reward_rate
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {rho R1 R2 switch12 switch21 : ℝ}
    {m z : Fin 2 → ℝ}
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hnonneg : 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1)
    (hparams :
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z)
    (haccept :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy) :
    Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
      μ arrival R1 R2 switch12 switch21 m z := by
  let P := Theorem3AcceptAllStructuredParameterData.of_evidence hparams
  exact
    { accept_all_optimal := haccept
      m0_eq := P.hm0
      arrival1_pos := A.harrival1_pos
      arrival2_pos := A.harrival2_pos
      switch12_pos := A.hswitch12_pos
      switch21_pos := A.hswitch21_pos
      acceptAll_mass_pos := by
        intro i
        fin_cases i
        · exact A.hmass1_pos
        · exact A.hmass2_pos
      time1_acceptAll_integrable := A.htime1_integrable
      time2_acceptAll_integrable := A.htime2_integrable
      q1_acceptAll_integrable := A.hq1_integrable
      q2_acceptAll_integrable := A.hq2_integrable
      nonsurge_after_surge_data := by
        intro ρ hρ
        have hsum21 : 0 < switch21 + switch12 := by
          linarith [A.hswitch21_pos, A.hswitch12_pos]
        have hfixed_exit_pos :
            0 <
              gn21ExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12 acceptAllPolicy :=
          gn21ExitWeightIntegral_pos_of_switch_pos
            (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
            (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
            measurableSet_acceptAllPolicy (fun _ hτ => hτ)
        have hfixed_time_pos :
            0 <
              gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
          gn21ScaledStateTime_pos_of_nonneg
            (μ 1) (arrival 1) acceptAllPolicy
            (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
            (fun _ hτ => hτ)
        have hfixed_A_pos :
            0 <
              gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
                  switch12 +
                gn21ExitWeightIntegral (μ 1) (arrival 1)
                  switch21 switch12 acceptAllPolicy :=
          add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
            hfixed_exit_pos
        have hfixed_mass :
            singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
          ne_of_gt A.hmass2_pos
        have hfixed_arrival_mass :
            arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy ≠ 0 :=
          mul_ne_zero (ne_of_gt A.harrival2_pos) hfixed_mass
        have hfixed_reward_rate :
            gn21MeasuredStateRewardRate (μ 1) (arrival 1)
                (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                acceptAllPolicy =
              R2 := by
          have hscaled :
              gn21ScaledStateEarning (μ 1) (arrival 1)
                  (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                  acceptAllPolicy =
                R2 * gn21ScaledStateTime (μ 1) (arrival 1)
                  acceptAllPolicy := by
            calc
              gn21ScaledStateEarning (μ 1) (arrival 1)
                  (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                  acceptAllPolicy
                  =
                m 1 *
                    (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
                  z 1 *
                    (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                        switch21 switch12 -
                      switch21) := by
                    simpa [ctmcStructuredDynamicSurgePrice,
                      ctmcDynamicSwitchProb, ctmcStructuredSurgePrice,
                      gn21AcceptAllScaledStateTime,
                      gn21AcceptAllExitWeightIntegral] using
                      paper_remark2_structured_scaled_earning_algebra
                        (μ 1) (arrival 1) (m 1) (z 1) switch21 switch12
                        acceptAllPolicy A.htime2_integrable
                        A.hq2_integrable
              _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
                P.surge_accounting
          exact
            gn21MeasuredStateRewardRate_eq_of_scaled_earning
              (μ 1) (arrival 1) R2
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              acceptAllPolicy hfixed_mass hfixed_arrival_mass
              (ne_of_gt hfixed_time_pos) hscaled
        exact
          ⟨P.nonsurgeRatio,
            GN21NonsurgeLemma10AcceptAllAggregateRewardRateData.of_acceptAll_tightening
              (hρ.1 0).1 (hρ.1 0).2 A.harrival1_pos A.hswitch12_pos
              A.hswitch21_pos
              (A.htime1_integrable.mono_set (hρ.1 0).1)
              (A.hq1_integrable.mono_set (hρ.1 0).1)
              A.htime1_integrable A.hq1_integrable
              P.nonsurge_acceptAll_bounds hfixed_A_pos
              (le_of_lt hfixed_exit_pos)
              (A.nonsurge_current_mass_pos m z hnonneg hparams ρ hρ.1)
              P.hz0 A.hR2_pos hfixed_mass hfixed_arrival_mass
              (ne_of_gt hfixed_time_pos) hfixed_reward_rate⟩
      surge_data := by
        intro ρ hρ
        exact A.surge_reward_rate_data m z hnonneg hparams ρ hρ.1 }

/--
Reward-rate-form Theorem 3 a.e.-uniqueness wrapper for the sequential surge
source route.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_feasible_sequential_surge_reward_rate_data_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases
      paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_reward_rate_data_assumptions
        μ arrival rho R1 R2 switch12 switch21 A with
    ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  have haccept :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy := by
    simpa [gn21MeasuredCTMCStructuredDynamicReward] using hIC
  have H :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_sequential_optimal_reward_rate_positive_response
      μ arrival R1 R2 switch12 switch21 m z
      (Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate.of_feasible_sequential_surge_reward_rate
        A hsigns hparams haccept)
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
    intro ρ hρ
    have hρ' :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) ρ := by
      simpa [gn21MeasuredCTMCStructuredDynamicReward] using hρ
    exact H.2 ρ hρ'
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

/--
Normalized Theorem 3 route with the paper-proof split made explicit:
feasible current-bounds data prove weak IC, while optimal-policy
positive-response data prove a.e. uniqueness.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_current_bounds_source_feasible_and_optimal_positive_response_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (feasible_current_bounds :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsSourceFeasibleCertificate
          μ arrival R1 R2 switch12 switch21 m z)
    (optimal_positive_response :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalSourcePositiveResponseCertificate
          μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_optimal_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (theorem3AcceptAllFeasibleWeakRewardCertificate_of_structured_current_bounds_source
      μ arrival R1 R2 switch12 switch21 feasible_current_bounds)
    optimal_positive_response

/--
Accounting-form version of the split current-bounds Theorem 3 route.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_current_bounds_accounting_feasible_and_optimal_positive_response_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (feasible_accounting :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsAccountingFeasibleCertificate
          μ arrival R1 R2 switch12 switch21 m z)
    (optimal_accounting :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalAccountingPositiveResponseCertificate
          μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_optimal_accounting_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (theorem3AcceptAllFeasibleWeakRewardCertificate_of_structured_current_bounds_accounting
      μ arrival R1 R2 switch12 switch21 feasible_accounting)
    optimal_accounting

/--
Reward-rate version of the split current-bounds Theorem 3 route.  This is the
closest Lean surface to the paper's local Lemma 9/10 notation.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_current_bounds_reward_rate_feasible_and_optimal_positive_response_normalized_mass_ratio_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (feasible_reward_rate :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsRewardRateFeasibleCertificate
          μ arrival R1 R2 switch12 switch21 m z)
    (optimal_reward_rate :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
        Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalRewardRatePositiveResponseCertificate
          μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (theorem3AcceptAllFeasibleWeakRewardCertificate_of_structured_current_bounds_reward_rate
      μ arrival R1 R2 switch12 switch21 feasible_reward_rate)
    optimal_reward_rate

end GN21DriverSurgePricing
