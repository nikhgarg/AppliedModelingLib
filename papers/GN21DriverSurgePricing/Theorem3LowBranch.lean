import GN21DriverSurgePricing.CTMCVerification

/-!
# GN21 Theorem 3 Low-Ratio Branch

This module records only direct algebraic consequences needed by a repaired
low-ratio proof.  In particular, it does not treat a policy-dependent Lemma 9
interval as a uniform certificate.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/--
The displayed source threshold is strictly below the ratio at which the
purely multiplicative non-surge calibration reaches the surge accounting
ceiling.  Thus, in the low-ratio branch, the surge multiplier can be selected
strictly above the calibrated non-surge multiplier.
-/
theorem theorem3_low_ratio_lt_surge_multiplier_ceiling
    (T1 T2 Q1 Q2 switch12 rho : ℝ)
    (hT1_pos : 0 < T1)
    (hT1_sub_one_pos : 0 < T1 - 1)
    (hT2_sub_one_pos : 0 < T2 - 1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hsecond_pos : 0 < T2 * switch12 + Q2)
    (hrho_lt_C :
      rho < theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12) :
    rho < T2 * (T1 - 1) / (T1 * (T2 - 1)) := by
  let D := theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12
  let N := theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12
  let A := T2 * (T1 - 1)
  let B := T1 * (T2 - 1)
  let S := T1 * D
  have hden_pos :
      0 < D := by
    dsimp [D]
    exact
    paper_theorem3_feasibility_denominator_pos_of_positive_pieces
      T1 T2 Q1 Q2 switch12 hQ2_pos hgap_pos hswitch12_pos
      (le_of_lt hsecond_pos)
  have hsource_den_pos :
      0 < S := by
    dsimp [S]
    exact mul_pos hT1_pos hden_pos
  have hceiling_den_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hT1_pos hT2_sub_one_pos
  have hthreshold_eq :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 = 1 - N / S := by
    rfl
  have hceiling_eq : T2 * (T1 - 1) / (T1 * (T2 - 1)) = A / B := by
    rfl
  have hscalar :
      A / B - (1 - N / S) = (A * S - B * S + B * N) / (B * S) := by
    field_simp [ne_of_gt hceiling_den_pos, ne_of_gt hsource_den_pos]
    ring
  have hfactor :
      A * S - B * S + B * N =
        T1 * ((T1 - 1) * Q2 * (switch12 * T1 - Q1) +
          (T2 * switch12 + Q2) *
            (switch12 * (T1 - 1) +
              (T2 - 1) * (Q1 - switch12))) := by
    dsimp [A, B, S, N, D, theorem3FeasibilityDenominator,
      theorem3FeasibilityNumerator]
    ring
  have hdiff :
      T2 * (T1 - 1) / (T1 * (T2 - 1)) -
          theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 =
        ((T1 - 1) * Q2 * (switch12 * T1 - Q1) +
          (T2 * switch12 + Q2) *
            (switch12 * (T1 - 1) +
              (T2 - 1) * (Q1 - switch12))) /
          ((T2 - 1) * S) := by
    rw [hthreshold_eq, hceiling_eq, hscalar, hfactor]
    field_simp [ne_of_gt hT1_pos]
    ring
  have hnum_pos :
      0 < (T1 - 1) * Q2 * (switch12 * T1 - Q1) +
        (T2 * switch12 + Q2) *
          (switch12 * (T1 - 1) +
            (T2 - 1) * (Q1 - switch12)) := by
    have hinner_pos :
        0 < switch12 * (T1 - 1) +
          (T2 - 1) * (Q1 - switch12) :=
      add_pos (mul_pos hswitch12_pos hT1_sub_one_pos)
        (mul_pos hT2_sub_one_pos hQ1_sub_switch12_pos)
    exact add_pos (mul_pos (mul_pos hT1_sub_one_pos hQ2_pos) hgap_pos)
      (mul_pos hsecond_pos hinner_pos)
  have hwhole_den_pos :
      0 < (T2 - 1) * S := mul_pos hT2_sub_one_pos hsource_den_pos
  have hdiff_pos :
      0 < T2 * (T1 - 1) / (T1 * (T2 - 1)) -
          theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 := by
    rw [hdiff]
    exact div_pos hnum_pos hwhole_den_pos
  exact lt_trans hrho_lt_C (sub_pos.mp hdiff_pos)

/--
After calibrating the non-surge multiplicative price to `R1`, the low-ratio
condition leaves strict room below the largest surge multiplier compatible
with the `R2` accounting equation.
-/
theorem theorem3_low_ratio_nonsurge_multiplier_lt_surge_ceiling
    (R1 R2 T1 T2 Q1 Q2 switch12 rho : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hT1_pos : 0 < T1)
    (hT1_sub_one_pos : 0 < T1 - 1)
    (hT2_sub_one_pos : 0 < T2 - 1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hsecond_pos : 0 < T2 * switch12 + Q2)
    (hrho_lt_C :
      rho < theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12) :
    R1 * T1 / (T1 - 1) < R2 * T2 / (T2 - 1) := by
  have hrho_lt_ceiling :
      rho < T2 * (T1 - 1) / (T1 * (T2 - 1)) :=
    theorem3_low_ratio_lt_surge_multiplier_ceiling
      T1 T2 Q1 Q2 switch12 rho hT1_pos hT1_sub_one_pos hT2_sub_one_pos
      hQ1_sub_switch12_pos hQ2_pos hswitch12_pos hgap_pos hsecond_pos
      hrho_lt_C
  have hden_pos : 0 < T1 * (T2 - 1) :=
    mul_pos hT1_pos hT2_sub_one_pos
  have hcross :
      rho * (T1 * (T2 - 1)) < T2 * (T1 - 1) :=
    (lt_div_iff₀ hden_pos).mp hrho_lt_ceiling
  have hratio : rho * T1 / (T1 - 1) < T2 / (T2 - 1) := by
    rw [div_lt_div_iff₀ hT1_sub_one_pos hT2_sub_one_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  rw [hR1_eq]
  calc
    rho * R2 * T1 / (T1 - 1) = R2 * (rho * T1 / (T1 - 1)) := by
      ring
    _ < R2 * (T2 / (T2 - 1)) :=
      mul_lt_mul_of_pos_left hratio hR2_pos
    _ = R2 * T2 / (T2 - 1) := by ring

/--
For a pure multiplicative non-surge price calibrated at accept-all, rejecting
some feasible trips cannot raise the one-state reward rate above the target
accept-all rate.  This is the actual uniform reward envelope available in the
low-ratio construction; it deliberately does not identify a current policy's
reward rate with the accept-all target.
-/
theorem gn21MeasuredStateRewardRate_multiplicativePricing_le_acceptAll_target
    (μ : Measure TripLength) (arrivalRate m R1 : ℝ)
    (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hm_nonneg : 0 ≤ m)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (htime_acceptAll_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hmass_pos : 0 < singleStateTripMass μ σ)
    (hmass_acceptAll_pos : 0 < singleStateTripMass μ acceptAllPolicy)
    (hacceptAll_reward :
      gn21MeasuredStateRewardRate μ arrivalRate (multiplicativePricing m)
        acceptAllPolicy = R1) :
    gn21MeasuredStateRewardRate μ arrivalRate (multiplicativePricing m) σ ≤
      R1 := by
  let T := gn21ScaledStateTime μ arrivalRate σ
  let Tbar := gn21ScaledStateTime μ arrivalRate acceptAllPolicy
  have hT_pos : 0 < T := by
    dsimp [T]
    exact gn21ScaledStateTime_pos_of_nonneg μ arrivalRate σ
      (le_of_lt harrival_pos) hσ_measurable hσ_subset
  have hTbar_pos : 0 < Tbar := by
    dsimp [Tbar]
    exact gn21ScaledStateTime_pos_of_nonneg μ arrivalRate acceptAllPolicy
      (le_of_lt harrival_pos) measurableSet_acceptAllPolicy
      (fun _ hτ => hτ)
  have hT_le : T ≤ Tbar := by
    dsimp [T, Tbar]
    exact gn21ScaledStateTime_le_acceptAll_of_subset μ arrivalRate σ
      (le_of_lt harrival_pos) htime_acceptAll_integrable hσ_subset
  have hfraction_le : (T - 1) / T ≤ (Tbar - 1) / Tbar := by
    apply (div_le_div_iff₀ hT_pos hTbar_pos).2
    nlinarith [hT_le]
  have hcurrent_formula :
      gn21MeasuredStateRewardRate μ arrivalRate (multiplicativePricing m) σ =
        m * (T - 1) / T := by
    rw [gn21MeasuredStateRewardRate_eq_scaled_primitives μ arrivalRate
      (multiplicativePricing m) σ (ne_of_gt hmass_pos)
      (mul_ne_zero (ne_of_gt harrival_pos) (ne_of_gt hmass_pos))]
    rw [gn21ScaledStateEarning_multiplicativePricing]
  have hacceptAll_formula :
      R1 = m * (Tbar - 1) / Tbar := by
    rw [← hacceptAll_reward]
    rw [gn21MeasuredStateRewardRate_eq_scaled_primitives μ arrivalRate
      (multiplicativePricing m) acceptAllPolicy
      (ne_of_gt hmass_acceptAll_pos)
      (mul_ne_zero (ne_of_gt harrival_pos) (ne_of_gt hmass_acceptAll_pos))]
    rw [gn21ScaledStateEarning_multiplicativePricing]
  calc
    gn21MeasuredStateRewardRate μ arrivalRate (multiplicativePricing m) σ =
        m * (T - 1) / T := hcurrent_formula
    _ = m * ((T - 1) / T) := by ring
    _ ≤ m * ((Tbar - 1) / Tbar) :=
      mul_le_mul_of_nonneg_left hfraction_le hm_nonneg
    _ = m * (Tbar - 1) / Tbar := by ring
    _ = R1 := hacceptAll_formula.symm

/--
Direct lower-endpoint verification for the first clause of GN21 Theorem 3.
The non-surge policy is the source-permitted cutoff-zero policy (the empty
open set), while the surge policy accepts all trips.  The low Bellman
condition is stated on the actual accept-all primitives; no policy-dependent
interval or selection certificate is used.
-/
theorem gn21_theorem3_empty_nonsurge_open_optimal_of_low_bellman_primitives
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (hR1_nonneg : 0 ≤ R1) (hR2_pos : 0 < R2)
    (hlow :
      switch12 * R1 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) ≤
        (R2 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1) * switch12 /
            (switch12 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1) +
              gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12)) *
          (switch12 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
            gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
              switch12 switch21))
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1) :
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
          rho := by
  let T0 : ℝ := gn21AcceptAllScaledStateTime (mu 0) (arrival 0)
  let T1 : ℝ := gn21AcceptAllScaledStateTime (mu 1) (arrival 1)
  let Q0 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
  let Q1 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
  have hsum12 : 0 < switch12 + switch21 := by linarith
  have hsum21 : 0 < switch21 + switch12 := by linarith
  have hq0_integrable :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hsum12
      (fun _ htau => htau) measurableSet_acceptAllPolicy htime1_integrable
  have hq1_integrable :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (mu 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hsum21
      (fun _ htau => htau) measurableSet_acceptAllPolicy htime2_integrable
  have hmass0_pos : 0 < singleStateTripMass (mu 0) acceptAllPolicy := by
    rw [hmass1_eq_one]
    norm_num
  have hmass1_pos : 0 < singleStateTripMass (mu 1) acceptAllPolicy := by
    rw [hmass2_eq_one]
    norm_num
  have hmeasure0_pos : 0 < (mu 0) acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos (mu 0) acceptAllPolicy hmass0_pos
  have hmeasure1_pos : 0 < (mu 1) acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos (mu 1) acceptAllPolicy hmass1_pos
  have hT0_pos : 0 < T0 := by
    dsimp [T0, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0)
      acceptAllPolicy (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy
      (fun _ htau => htau)
  have hT1_pos : 0 < T1 := by
    dsimp [T1, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1)
      acceptAllPolicy (le_of_lt harrival2_pos) measurableSet_acceptAllPolicy
      (fun _ htau => htau)
  have hQ0_pos : 0 < Q0 := by
    dsimp [Q0, gn21AcceptAllExitWeightIntegral]
    exact gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
      switch12 switch21 acceptAllPolicy (le_of_lt harrival1_pos)
      hswitch12_pos hsum12 measurableSet_acceptAllPolicy (fun _ htau => htau)
  have hQ1_pos : 0 < Q1 := by
    dsimp [Q1, gn21AcceptAllExitWeightIntegral]
    exact gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
      switch21 switch12 acceptAllPolicy (le_of_lt harrival2_pos)
      hswitch21_pos hsum21 measurableSet_acceptAllPolicy (fun _ htau => htau)
  have hT0_sub_one_pos : 0 < T0 - 1 := by
    dsimp [T0, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_sub_one_pos_of_acceptAll_measure_pos
      (mu 0) (arrival 0) harrival1_pos htime1_integrable hmeasure0_pos
  have hT1_sub_one_pos : 0 < T1 - 1 := by
    dsimp [T1, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_sub_one_pos_of_acceptAll_measure_pos
      (mu 1) (arrival 1) harrival2_pos htime2_integrable hmeasure1_pos
  have hQ0_sub_switch_pos : 0 < Q0 - switch12 := by
    dsimp [Q0, gn21AcceptAllExitWeightIntegral]
    exact sub_pos.mpr
      (paper_remark4_exit_weight_gt_switch_of_positive_measure
        (mu 0) (arrival 0) switch12 switch21 acceptAllPolicy
        harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
        (fun _ htau => htau) hq0_integrable hmeasure0_pos)
  have hQ1_sub_switch_pos : 0 < Q1 - switch21 := by
    dsimp [Q1, gn21AcceptAllExitWeightIntegral]
    exact sub_pos.mpr
      (paper_remark4_exit_weight_gt_switch_of_positive_measure
        (mu 1) (arrival 1) switch21 switch12 acceptAllPolicy
        harrival2_pos hswitch21_pos hsum21 measurableSet_acceptAllPolicy
        (fun _ htau => htau) hq1_integrable hmeasure1_pos)
  have hgap0_pos : 0 < switch12 * T0 - Q0 := by
    dsimp [T0, Q0, gn21AcceptAllScaledStateTime,
      gn21AcceptAllExitWeightIntegral]
    exact paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
      (mu 0) (arrival 0) switch12 switch21 acceptAllPolicy
      harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
      (fun _ htau => htau) htime1_integrable hq0_integrable hmeasure0_pos
  let D : ℝ := switch12 * T1 + Q1
  have hD_pos : 0 < D := by
    dsimp [D]
    exact add_pos (mul_pos hswitch12_pos hT1_pos) hQ1_pos
  let g : ℝ := R2 * T1 * switch12 / D
  let d0 : ℝ := -(g / switch12)
  let d1 : ℝ := g / switch12
  let m0 : ℝ := (R1 * T0 - d0 * (Q0 - switch12)) / (T0 - 1)
  let a1 : ℝ := T1 - 1
  let b1 : ℝ := Q1 - switch21
  let c1 : ℝ := g + d1 * switch21
  let u : ℝ := c1 / (2 * a1)
  let v : ℝ := c1 / (2 * b1)
  let m1 : ℝ := g + u
  let z1 : ℝ := d1 + v
  have hg_pos : 0 < g := by
    dsimp [g]
    exact div_pos (mul_pos (mul_pos hR2_pos hT1_pos) hswitch12_pos) hD_pos
  have hd0_neg : d0 < 0 := by
    dsimp [d0]
    exact neg_lt_zero.mpr (div_pos hg_pos hswitch12_pos)
  have hd1_pos : 0 < d1 := by
    dsimp [d1]
    exact div_pos hg_pos hswitch12_pos
  have hconstant : g + d0 * switch12 = 0 := by
    dsimp [d0]
    field_simp [ne_of_gt hswitch12_pos]
    ring
  have hstate0 :
      R1 * T0 = m0 * (T0 - 1) + d0 * (Q0 - switch12) := by
    rw [show m0 =
      (R1 * T0 - d0 * (Q0 - switch12)) / (T0 - 1) by rfl]
    field_simp [ne_of_gt hT0_sub_one_pos]
    ring
  have hstate1 : R2 * T1 = g * T1 + d1 * Q1 := by
    dsimp [g, d1, D]
    field_simp [ne_of_gt hswitch12_pos, ne_of_gt hD_pos]
  have hlow' :
      switch12 * R1 * T0 ≤ g * (switch12 * T0 - Q0) := by
    simpa [T0, T1, Q0, Q1, g, D] using hlow
  have hnum0_nonneg : 0 ≤ R1 * T0 - d0 * (Q0 - switch12) := by
    have hleft : 0 ≤ R1 * T0 :=
      mul_nonneg hR1_nonneg (le_of_lt hT0_pos)
    have hright : d0 * (Q0 - switch12) < 0 :=
      mul_neg_of_neg_of_pos hd0_neg hQ0_sub_switch_pos
    linarith
  have hm0_nonneg : 0 ≤ m0 := by
    rw [show m0 =
      (R1 * T0 - d0 * (Q0 - switch12)) / (T0 - 1) by rfl]
    exact div_nonneg hnum0_nonneg (le_of_lt hT0_sub_one_pos)
  have hm0_le_g : m0 ≤ g := by
    rw [show m0 =
      (R1 * T0 - d0 * (Q0 - switch12)) / (T0 - 1) by rfl]
    apply (div_le_iff₀ hT0_sub_one_pos).2
    rw [← sub_nonpos]
    have hdiff :
        (R1 * T0 - d0 * (Q0 - switch12)) - g * (T0 - 1) =
          (switch12 * R1 * T0 - g * (switch12 * T0 - Q0)) / switch12 := by
      dsimp [d0]
      field_simp [ne_of_gt hswitch12_pos]
      ring
    rw [hdiff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hlow'])
      (le_of_lt hswitch12_pos)
  have ha1_pos : 0 < a1 := by simpa [a1] using hT1_sub_one_pos
  have hb1_pos : 0 < b1 := by simpa [b1] using hQ1_sub_switch_pos
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    exact add_pos hg_pos (mul_pos hd1_pos hswitch21_pos)
  have hu_pos : 0 < u := by
    dsimp [u]
    exact div_pos hc1_pos (mul_pos (by norm_num) ha1_pos)
  have hv_pos : 0 < v := by
    dsimp [v]
    exact div_pos hc1_pos (mul_pos (by norm_num) hb1_pos)
  have hm1_pos : 0 < m1 := by
    dsimp [m1]
    exact add_pos hg_pos hu_pos
  have hz1_nonneg : 0 ≤ z1 := by
    dsimp [z1]
    exact add_nonneg (le_of_lt hd1_pos) (le_of_lt hv_pos)
  have haccount1 :
      m1 * (T1 - 1) + z1 * (Q1 - switch21) = R2 * T1 := by
    rw [hstate1]
    have hrearrange :
        g * T1 + d1 * Q1 = g * a1 + d1 * b1 + c1 := by
      dsimp [a1, b1, c1]
      ring
    rw [hrearrange]
    dsimp [m1, z1, u, v]
    field_simp [ne_of_gt ha1_pos, ne_of_gt hb1_pos]
    ring
  let m : Fin 2 → ℝ := fun i => if i = 0 then m0 else m1
  let z : Fin 2 → ℝ := fun i => if i = 0 then d0 else z1
  have hm0 : m 0 = m0 := by simp [m]
  have hm1 : m 1 = m1 := by simp [m]
  have hz0 : z 0 = d0 := by simp [z]
  have hz1 : z 1 = z1 := by simp [z]
  have hW0_target :
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy = R1 * T0 := by
    calc
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        m0 * (T0 - 1) + d0 * (Q0 - switch12) := by
          simpa [T0, Q0, ctmcStructuredDynamicSurgePrice,
            ctmcDynamicSwitchProb, m, z] using
            (paper_remark2_structured_scaled_earning_algebra
              (mu 0) (arrival 0) m0 d0 switch12 switch21 acceptAllPolicy
              htime1_integrable hq0_integrable)
      _ = R1 * T0 := hstate0.symm
  have hW1_target :
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy = R2 * T1 := by
    calc
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        m1 * (T1 - 1) + z1 * (Q1 - switch21) := by
          simpa [T1, Q1, ctmcStructuredDynamicSurgePrice,
            ctmcDynamicSwitchProb, m, z] using
            (paper_remark2_structured_scaled_earning_algebra
              (mu 1) (arrival 1) m1 z1 switch21 switch12 acceptAllPolicy
              htime2_integrable hq1_integrable)
      _ = R2 * T1 := haccount1
  have hrate0 :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy = R1 := by
    have hendpoint :=
      gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
        (mu 0) (arrival 0)
        (gn21MeasuredStateRewardRate (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        acceptAllPolicy harrival1_pos measurableSet_acceptAllPolicy
        (fun _ htau => htau) rfl
    have hTpos :
        0 < gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy := by
      simpa [T0, gn21AcceptAllScaledStateTime] using hT0_pos
    apply mul_right_cancel₀ (ne_of_gt hTpos)
    calc
      gn21MeasuredStateRewardRate (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy *
          gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy =
        gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy := hendpoint.symm
      _ = R1 * gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy := by
        simpa [T0, gn21AcceptAllScaledStateTime] using hW0_target
  have hrate1 :
      gn21MeasuredStateRewardRate (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy = R2 := by
    have hendpoint :=
      gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
        (mu 1) (arrival 1)
        (gn21MeasuredStateRewardRate (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        acceptAllPolicy harrival2_pos measurableSet_acceptAllPolicy
        (fun _ htau => htau) rfl
    have hTpos :
        0 < gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy := by
      simpa [T1, gn21AcceptAllScaledStateTime] using hT1_pos
    apply mul_right_cancel₀ (ne_of_gt hTpos)
    calc
      gn21MeasuredStateRewardRate (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy *
          gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy =
        gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy := hendpoint.symm
      _ = R2 * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy := by
        simpa [T1, gn21AcceptAllScaledStateTime] using hW1_target
  have haccounting1 :
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        g * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy +
          d1 * gn21ExitWeightIntegral (mu 1) (arrival 1)
            switch21 switch12 acceptAllPolicy := by
    rw [hW1_target]
    simpa [T1, Q1] using hstate1
  let rho : Fin 2 → TripPolicy :=
    fun i => if i = 0 then (∅ : TripPolicy) else acceptAllPolicy
  have hrho0 : rho 0 = (∅ : TripPolicy) := by simp [rho]
  have hrho1 : rho 1 = acceptAllPolicy := by simp [rho]
  have hrho_feasible : dynamicFeasibleOpenPolicy rho := by
    intro i
    fin_cases i
    · exact ⟨by simp [rho], by simp [rho]⟩
    · constructor
      · simp [rho]
      · simpa [rho, acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
          (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  have hrho_cutoff : rejectsLongTripsFiniteOrInfiniteCutoff (rho 0) := by
    left
    refine ⟨0, ?_⟩
    intro tau htau
    simp [rho, not_lt_of_ge (le_of_lt htau)]
  have haggregate_rho :
      gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
        rho = g := by
    have haggregate :
        gn21AggregateDynamicReward switch12 Q1 1 T1 0 (R2 * T1) = g := by
      unfold gn21AggregateDynamicReward
      dsimp [g, D]
      field_simp [ne_of_gt hD_pos]
      ring
    change
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
          (gn21ScaledStateEarning (mu 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (rho 0))
          (gn21ScaledStateEarning (mu 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (rho 1)) = g
    rw [hrho0, hrho1, gn21ExitWeightIntegral_empty,
      gn21ScaledStateTime_empty, gn21ScaledStateEarning_empty, hW1_target]
    simpa [T1, Q1] using haggregate
  have hopen : dynamicOpenOptimal
      (gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z)
      rho := by
    refine ⟨hrho_feasible, ?_⟩
    intro sigma hsigma
    let T0s : ℝ := gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0)
    let T1s : ℝ := gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1)
    let Q0s : ℝ :=
      gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (sigma 0)
    let Q1s : ℝ :=
      gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (sigma 1)
    let W0s : ℝ := gn21ScaledStateEarning (mu 0) (arrival 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0)
    let W1s : ℝ := gn21ScaledStateEarning (mu 1) (arrival 1)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)
    have hsigma0_meas : MeasurableSet (sigma 0) := (hsigma 0).2.measurableSet
    have hsigma1_meas : MeasurableSet (sigma 1) := (hsigma 1).2.measurableSet
    have htime0_sigma := htime1_integrable.mono_set (hsigma 0).1
    have htime1_sigma := htime2_integrable.mono_set (hsigma 1).1
    have hq0_sigma := hq0_integrable.mono_set (hsigma 0).1
    have hq1_sigma := hq1_integrable.mono_set (hsigma 1).1
    have hw0_integrable : IntegrableOn
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        acceptAllPolicy (mu 0) := by
      apply integrableOn_ctmcStructuredDynamicSurgePrice
      · exact htime1_integrable
      · simpa [ctmcDynamicSwitchProb] using hq0_integrable
    have hw1_integrable : IntegrableOn
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        acceptAllPolicy (mu 1) := by
      apply integrableOn_ctmcStructuredDynamicSurgePrice
      · exact htime2_integrable
      · simpa [ctmcDynamicSwitchProb] using hq1_integrable
    have henvelope0 : ∀ tau : TripLength, tau ∈ sigma 0 →
        ctmcStructuredDynamicSurgePrice m z switch12 switch21 0 tau -
          g * tau - d0 * gn21SwitchProb switch12 switch21 tau ≤ 0 := by
      intro tau htau
      have htau_pos : 0 < tau := (hsigma 0).1 htau
      calc
        ctmcStructuredDynamicSurgePrice m z switch12 switch21 0 tau -
            g * tau - d0 * gn21SwitchProb switch12 switch21 tau =
          (m0 - g) * tau := by
            simp [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
              structuredSurgePrice, m, z]
            ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr hm0_le_g) (le_of_lt htau_pos)
    have henvelope1 : ∀ tau : TripLength, 0 < tau →
        0 ≤ ctmcStructuredDynamicSurgePrice m z switch12 switch21 1 tau -
          g * tau - d1 * gn21SwitchProb switch21 switch12 tau := by
      intro tau htau
      have hq_nonneg : 0 ≤ gn21SwitchProb switch21 switch12 tau :=
        paper_lemma2_switch_probability_nonneg switch21 switch12 tau
          (le_of_lt hswitch21_pos) hsum21 (le_of_lt htau)
      have htime_term : 0 ≤ u * tau :=
        mul_nonneg (le_of_lt hu_pos) (le_of_lt htau)
      have hq_term : 0 ≤ v * gn21SwitchProb switch21 switch12 tau :=
        mul_nonneg (le_of_lt hv_pos) hq_nonneg
      calc
        0 ≤ u * tau + v * gn21SwitchProb switch21 switch12 tau :=
          add_nonneg htime_term hq_term
        _ = ctmcStructuredDynamicSurgePrice m z switch12 switch21 1 tau -
            g * tau - d1 * gn21SwitchProb switch21 switch12 tau := by
          simp [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
            structuredSurgePrice, m, z]
          ring
    have hW0_bound : W0s ≤ g * T0s + d0 * Q0s := by
      dsimp [W0s, T0s, Q0s]
      exact gn21ScaledStateEarning_le_bellman_envelope_of_nonpos
        (mu 0) (arrival 0) switch12 switch21 g d0
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0)
        (le_of_lt harrival1_pos) hsigma0_meas htime0_sigma hq0_sigma
        (hw0_integrable.mono_set (hsigma 0).1) hconstant henvelope0
    have hW1_bound : W1s ≤ g * T1s + d1 * Q1s := by
      dsimp [W1s, T1s, Q1s]
      exact gn21ScaledStateEarning_le_bellman_envelope
        (mu 1) (arrival 1) switch21 switch12 g d1
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)
        (le_of_lt harrival2_pos) (hsigma 1).1
        htime2_integrable hq1_integrable hw1_integrable haccounting1
        henvelope1
    have hT0s_pos : 0 < T0s := by
      dsimp [T0s]
      exact gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (sigma 0)
        (le_of_lt harrival1_pos) hsigma0_meas (hsigma 0).1
    have hT1s_pos : 0 < T1s := by
      dsimp [T1s]
      exact gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (sigma 1)
        (le_of_lt harrival2_pos) hsigma1_meas (hsigma 1).1
    have hQ0s_pos : 0 < Q0s := by
      dsimp [Q0s]
      exact gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
        switch12 switch21 (sigma 0) (le_of_lt harrival1_pos)
        hswitch12_pos hsum12 hsigma0_meas (hsigma 0).1
    have hQ1s_pos : 0 < Q1s := by
      dsimp [Q1s]
      exact gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
        switch21 switch12 (sigma 1) (le_of_lt harrival2_pos)
        hswitch21_pos hsum21 hsigma1_meas (hsigma 1).1
    have haggregate :
        gn21AggregateDynamicReward Q0s Q1s T0s T1s W0s W1s ≤ g :=
      gn21AggregateDynamicReward_le_of_bellman_envelopes
        Q0s Q1s T0s T1s W0s W1s g d0 d1
        hQ0s_pos hQ1s_pos hT0s_pos hT1s_pos hW0_bound hW1_bound (by
          dsimp [d0, d1]
          ring)
    change gn21AggregateDynamicReward Q0s Q1s T0s T1s W0s W1s ≤
      gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z rho
    rw [haggregate_rho]
    exact haggregate
  exact ⟨m, z, rho, ⟨hm0_nonneg, le_of_lt hm1_pos, hz1_nonneg⟩,
    hrate0, hrate1, hrho1, hrho_cutoff, hopen⟩

/--
The scalar split condition for the cutoff-zero endpoint is exactly the
complementary weak inequality to the direct accept-all Bellman condition.
-/
theorem theorem3_low_bellman_condition_of_ratio_le
    (R1 R2 T0 T1 Q0 Q1 switch12 : ℝ)
    (hR2_pos : 0 < R2)
    (hT0_pos : 0 < T0) (hT1_pos : 0 < T1)
    (hQ1_pos : 0 < Q1) (hswitch12_pos : 0 < switch12)
    (hratio_le :
      R1 / R2 ≤ T1 * (switch12 * T0 - Q0) /
        (T0 * (Q1 + switch12 * T1))) :
    switch12 * R1 * T0 ≤
      (R2 * T1 * switch12 / (switch12 * T1 + Q1)) *
        (switch12 * T0 - Q0) := by
  have hBden_pos : 0 < T0 * (Q1 + switch12 * T1) :=
    mul_pos hT0_pos (add_pos hQ1_pos (mul_pos hswitch12_pos hT1_pos))
  have hD_pos : 0 < switch12 * T1 + Q1 :=
    add_pos (mul_pos hswitch12_pos hT1_pos) hQ1_pos
  have hcross :
      R1 * (T0 * (Q1 + switch12 * T1)) ≤
        (T1 * (switch12 * T0 - Q0)) * R2 :=
    (div_le_div_iff₀ hR2_pos hBden_pos).mp hratio_le
  have hscaled_raw :=
    mul_le_mul_of_nonneg_left hcross (le_of_lt hswitch12_pos)
  have hscaled :
      switch12 * R1 * T0 * (switch12 * T1 + Q1) ≤
        R2 * T1 * switch12 * (switch12 * T0 - Q0) := by
    calc
      switch12 * R1 * T0 * (switch12 * T1 + Q1) =
          switch12 * (R1 * (T0 * (Q1 + switch12 * T1))) := by ring
      _ ≤ switch12 * ((T1 * (switch12 * T0 - Q0)) * R2) := hscaled_raw
      _ = R2 * T1 * switch12 * (switch12 * T0 - Q0) := by ring
  have htarget :
      switch12 * R1 * T0 ≤
        R2 * T1 * switch12 * (switch12 * T0 - Q0) /
          (switch12 * T1 + Q1) :=
    (le_div_iff₀ hD_pos).2 hscaled
  calc
    switch12 * R1 * T0 ≤
        R2 * T1 * switch12 * (switch12 * T0 - Q0) /
          (switch12 * T1 + Q1) := htarget
    _ = (R2 * T1 * switch12 / (switch12 * T1 + Q1)) *
          (switch12 * T0 - Q0) := by ring

/--
The internal real-valued construction for the first clause of GN21 Theorem 3.
The proof partitions the target ratio at the actual Bellman threshold: the low
side uses the literal zero cutoff and the high side uses accept-all.
-/
theorem gn21_theorem3_structured_open_optimal_of_nonnegative_target_rates
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (hR1_nonneg : 0 ≤ R1) (hR1_lt_R2 : R1 < R2)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime2_integrable :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hmass1_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1) :
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
          rho := by
  have hR2_pos : 0 < R2 := lt_of_le_of_lt hR1_nonneg hR1_lt_R2
  have hratio_lt_one : R1 / R2 < 1 := by
    apply (div_lt_iff₀ hR2_pos).2
    simpa using hR1_lt_R2
  let T0 : ℝ := gn21AcceptAllScaledStateTime (mu 0) (arrival 0)
  let T1 : ℝ := gn21AcceptAllScaledStateTime (mu 1) (arrival 1)
  let Q0 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
  let Q1 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
  have hsum12 : 0 < switch12 + switch21 := by linarith
  have hsum21 : 0 < switch21 + switch12 := by linarith
  have hT0_pos : 0 < T0 := by
    dsimp [T0, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0)
      acceptAllPolicy (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy
      (fun _ htau => htau)
  have hT1_pos : 0 < T1 := by
    dsimp [T1, gn21AcceptAllScaledStateTime]
    exact gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1)
      acceptAllPolicy (le_of_lt harrival2_pos) measurableSet_acceptAllPolicy
      (fun _ htau => htau)
  have hQ1_pos : 0 < Q1 := by
    dsimp [Q1, gn21AcceptAllExitWeightIntegral]
    exact gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
      switch21 switch12 acceptAllPolicy (le_of_lt harrival2_pos)
      hswitch21_pos hsum21 measurableSet_acceptAllPolicy (fun _ htau => htau)
  by_cases hratio_low :
      R1 / R2 ≤ T1 * (switch12 * T0 - Q0) /
        (T0 * (Q1 + switch12 * T1))
  · have hlow_direct :
        switch12 * R1 * T0 ≤
          (R2 * T1 * switch12 / (switch12 * T1 + Q1)) *
            (switch12 * T0 - Q0) :=
      theorem3_low_bellman_condition_of_ratio_le
        R1 R2 T0 T1 Q0 Q1 switch12 hR2_pos hT0_pos hT1_pos hQ1_pos
        hswitch12_pos hratio_low
    have hlow :
        switch12 * R1 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) ≤
          (R2 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1) * switch12 /
              (switch12 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1) +
                gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                  switch21 switch12)) *
            (switch12 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
              gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
                switch12 switch21) := by
      simpa [T0, T1, Q0, Q1] using hlow_direct
    exact gn21_theorem3_empty_nonsurge_open_optimal_of_low_bellman_primitives
      mu arrival R1 R2 switch12 switch21 hR1_nonneg hR2_pos hlow
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one
  · have hbellman :
        T1 * (switch12 * T0 - Q0) /
            (T0 * (Q1 + switch12 * T1)) < R1 / R2 :=
      lt_of_not_ge hratio_low
    have hbellman_raw :
        gn21AcceptAllScaledStateTime (mu 1) (arrival 1) *
            (switch12 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
              gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
                switch12 switch21) /
            (gn21AcceptAllScaledStateTime (mu 0) (arrival 0) *
              (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12 +
                switch12 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1))) <
          R1 / R2 := by
      simpa [T0, T1, Q0, Q1] using hbellman
    rcases gn21_theorem3_structured_open_ic_of_bellman_primitives
        mu arrival R1 R2 switch12 switch21 hR2_pos hbellman_raw hratio_lt_one
        harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one with
      ⟨m, z, hparams, hrate0, hrate1, hopen, _hunique⟩
    refine ⟨m, z, acceptAllDynamicPolicy, hparams, hrate0, hrate1, ?_, ?_, hopen⟩
    · rfl
    · exact Or.inr acceptsAllTrips_acceptAllPolicy

end

end GN21DriverSurgePricing
