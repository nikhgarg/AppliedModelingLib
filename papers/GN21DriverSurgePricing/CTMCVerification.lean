import GN21DriverSurgePricing.DomainBridge

/-!
# Direct Aggregate Verification for GN21 Theorem 3

This module verifies accept-all optimality directly against the Appendix-D
`Q,T,W` aggregate objective.  It avoids the invalid quantifier exchange in the
printed Lemma 9 interval argument: the constructed price is fixed from the
accept-all primitives before any deviation policy is considered.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-- The source threshold is stronger than the Bellman-envelope threshold
needed for the non-surge state. -/
theorem theorem3_bellman_nonsurge_threshold_lt_of_source_ratio
    (T1 T2 Q1 Q2 switch12 rho : ℝ)
    (hC_lt_rho : theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hT1_pos : 0 < T1) (hT2_pos : 0 < T2)
    (hQ1_pos : 0 < Q1) (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hgap_pos : 0 < switch12 * T1 - Q1) :
    T2 * (switch12 * T1 - Q1) /
        (T1 * (Q2 + switch12 * T2)) < rho := by
  let gap := switch12 * T1 - Q1
  let P := Q2 + switch12 * T2
  let D := theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12
  have hP_pos : 0 < P := by
    dsimp [P]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D, theorem3FeasibilityDenominator]
    exact add_pos (mul_pos hQ2_pos hgap_pos)
      (mul_pos hswitch12_pos (by positivity))
  have hscaledD_pos : 0 < T1 * D := mul_pos hT1_pos hD_pos
  have hsource_eq :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 =
        gap * (T1 * Q2 + switch12 * T2) / (T1 * D) := by
    dsimp [theorem3FeasibilityThresholdC, theorem3FeasibilityNumerator,
      theorem3FeasibilityDenominator, gap, D]
    field_simp [ne_of_gt hscaledD_pos]
    ring
  have hsource_gt :
      T2 * gap / (T1 * P) <
        gap * (T1 * Q2 + switch12 * T2) / (T1 * D) := by
    have hleft_den_pos : 0 < T1 * P := mul_pos hT1_pos hP_pos
    rw [div_lt_div_iff₀ hleft_den_pos hscaledD_pos]
    have hfactor :
        gap * (T1 * Q2 + switch12 * T2) * (T1 * P) -
            T2 * gap * (T1 * D) =
          gap * T1 * Q2 * (T1 * Q2 + T2 * Q1) := by
      dsimp [D, P, theorem3FeasibilityDenominator, gap]
      ring
    rw [← sub_pos]
    rw [hfactor]
    positivity
  rw [hsource_eq] at hC_lt_rho
  exact hsource_gt.trans hC_lt_rho

/-- Fixed structured-price coefficients from Bellman accounting data.  Both
trip-time and switch-probability coefficients have strict positive slack, so
the resulting accept-all comparison is strict off null sets. -/
theorem gn21BellmanStructuredParameters_exist
    (T0 T1 Q0 Q1 R0 R1 switch01 switch10 g d0 d1 : ℝ)
    (hT0_sub_one_pos : 0 < T0 - 1)
    (hT1_sub_one_pos : 0 < T1 - 1)
    (hQ0_sub_switch_pos : 0 < Q0 - switch01)
    (hQ1_sub_switch_pos : 0 < Q1 - switch10)
    (hg_pos : 0 < g) (hd1_nonneg : 0 ≤ d1)
    (hstate0 : R0 * T0 = g * T0 + d0 * Q0)
    (hstate1 : R1 * T1 = g * T1 + d1 * Q1)
    (hslack0 : 0 < g + d0 * switch01)
    (hslack1 : 0 < g + d1 * switch10) :
    ∃ m0 m1 z0 z1 : ℝ,
      0 < m0 ∧ 0 < m1 ∧ 0 ≤ z1 ∧
        m0 * (T0 - 1) + z0 * (Q0 - switch01) = R0 * T0 ∧
        m1 * (T1 - 1) + z1 * (Q1 - switch10) = R1 * T1 ∧
        0 < m0 - g ∧ 0 < z0 - d0 ∧
        0 < m1 - g ∧ 0 < z1 - d1 := by
  let a0 := T0 - 1
  let a1 := T1 - 1
  let b0 := Q0 - switch01
  let b1 := Q1 - switch10
  let c0 := g + d0 * switch01
  let c1 := g + d1 * switch10
  have ha0_pos : 0 < a0 := by simpa [a0] using hT0_sub_one_pos
  have ha1_pos : 0 < a1 := by simpa [a1] using hT1_sub_one_pos
  have hb0_pos : 0 < b0 := by simpa [b0] using hQ0_sub_switch_pos
  have hb1_pos : 0 < b1 := by simpa [b1] using hQ1_sub_switch_pos
  have hc0_pos : 0 < c0 := by simpa [c0] using hslack0
  have hc1_pos : 0 < c1 := by simpa [c1] using hslack1
  let x0 := c0 / (2 * a0)
  let x1 := c1 / (2 * a1)
  let y0 := c0 / (2 * b0)
  let y1 := c1 / (2 * b1)
  have hx0_pos : 0 < x0 := by
    exact div_pos hc0_pos (mul_pos (by norm_num) ha0_pos)
  have hx1_pos : 0 < x1 := by
    exact div_pos hc1_pos (mul_pos (by norm_num) ha1_pos)
  have hy0_pos : 0 < y0 := by
    exact div_pos hc0_pos (mul_pos (by norm_num) hb0_pos)
  have hy1_pos : 0 < y1 := by
    exact div_pos hc1_pos (mul_pos (by norm_num) hb1_pos)
  refine ⟨g + x0, g + x1, d0 + y0, d1 + y1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact add_pos hg_pos hx0_pos
  · exact add_pos hg_pos hx1_pos
  · exact add_nonneg hd1_nonneg (le_of_lt hy1_pos)
  · rw [hstate0]
    have hsum0 : g * T0 + d0 * Q0 = g * a0 + d0 * b0 + c0 := by
      dsimp [a0, b0, c0]
      ring
    rw [hsum0]
    dsimp [x0, y0]
    field_simp [ne_of_gt ha0_pos, ne_of_gt hb0_pos]
    ring
  · rw [hstate1]
    have hsum1 : g * T1 + d1 * Q1 = g * a1 + d1 * b1 + c1 := by
      dsimp [a1, b1, c1]
      ring
    rw [hsum1]
    dsimp [x1, y1]
    field_simp [ne_of_gt ha1_pos, ne_of_gt hb1_pos]
    ring
  · change 0 < (g + x0) - g
    linarith
  · change 0 < (d0 + y0) - d0
    linarith
  · change 0 < (g + x1) - g
    linarith
  · change 0 < (d1 + y1) - d1
    linarith

/-- Positive accept-all trip mass gives strictly more than the unit waiting
term in the scaled state-time primitive. -/
theorem gn21ScaledStateTime_sub_one_pos_of_acceptAll_measure_pos
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (harrival_pos : 0 < arrivalRate)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hmeasure_pos : 0 < μ acceptAllPolicy) :
    0 < gn21ScaledStateTime μ arrivalRate acceptAllPolicy - 1 := by
  have htime_nonneg :
      0 ≤ᵐ[μ.restrict acceptAllPolicy] (fun τ : TripLength => τ) :=
    (ae_restrict_iff' measurableSet_acceptAllPolicy).2
      (Filter.Eventually.of_forall fun τ hτ => le_of_lt hτ)
  have hsupport : Function.support (fun τ : TripLength => τ) ∩
      acceptAllPolicy = acceptAllPolicy := by
    ext τ
    constructor
    · exact fun hτ => hτ.2
    · intro hτ
      exact ⟨ne_of_gt hτ, hτ⟩
  have htime_pos : 0 < ∫ τ in acceptAllPolicy, τ ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae htime_nonneg htime_integrable).2
      (by simpa [hsupport] using hmeasure_pos)
  unfold gn21ScaledStateTime singleStateTripTime
  nlinarith [mul_pos harrival_pos htime_pos]

/-- Expanding a statewise Bellman advantage into the Appendix-D `Q,T,W`
primitives. -/
theorem gn21ScaledStateEarning_bellman_surplus_eq
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI g d : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        σ μ)
    (hw_integrable : IntegrableOn w σ μ) :
    arrivalRate * ∫ τ in σ,
        (w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ) ∂μ =
      gn21ScaledStateEarning μ arrivalRate w σ -
        g * gn21ScaledStateTime μ arrivalRate σ -
          d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
            g + d * switchIJ := by
  have hadvantage_integral :
      ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ =
        ∫ τ in σ, w τ ∂μ - g * ∫ τ in σ, τ ∂μ -
          d * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
    calc
      ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ =
          ∫ τ in σ, ((w - fun τ => g * τ) -
            fun τ => d * gn21SwitchProb switchIJ switchJI τ) τ ∂μ := by
              rfl
      _ = ∫ τ in σ, w τ - g * τ ∂μ -
            ∫ τ in σ, d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              simpa only [Pi.sub_apply] using
                (integral_sub (hw_integrable.sub (htime_integrable.const_mul g))
                  (hq_integrable.const_mul d))
      _ = (∫ τ in σ, w τ ∂μ - ∫ τ in σ, g * τ ∂μ) -
            ∫ τ in σ, d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_sub hw_integrable (htime_integrable.const_mul g)]
      _ = ∫ τ in σ, w τ ∂μ - g * ∫ τ in σ, τ ∂μ -
            d * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_const_mul, integral_const_mul]
  rw [hadvantage_integral]
  unfold gn21ScaledStateEarning gn21ScaledStateTime gn21ExitWeightIntegral
    singleStateTripPayment singleStateTripTime
  ring

/--
A nonpositive pointwise Bellman advantage bounds a state's scaled earning
without selecting an accept-all comparison policy.  This is the endpoint form
needed when the source's admissible cutoff is zero and the candidate policy is
empty.
-/
theorem gn21ScaledStateEarning_le_bellman_envelope_of_nonpos
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI g d : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        σ μ)
    (hw_integrable : IntegrableOn w σ μ)
    (hconstant : g + d * switchIJ = 0)
    (henvelope : ∀ τ : TripLength, τ ∈ σ →
      w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ≤ 0) :
    gn21ScaledStateEarning μ arrivalRate w σ ≤
      g * gn21ScaledStateTime μ arrivalRate σ +
        d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  have hintegral_nonpos :
      ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ ≤ 0 :=
    setIntegral_nonpos hσ_measurable henvelope
  have hscaled_nonpos :
      arrivalRate *
          ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ ≤
        0 :=
    mul_nonpos_of_nonneg_of_nonpos harrival_nonneg hintegral_nonpos
  have hsurplus :=
    gn21ScaledStateEarning_bellman_surplus_eq μ arrivalRate switchIJ switchJI
      g d w σ htime_integrable hq_integrable hw_integrable
  have hsurplus' :
      arrivalRate *
          ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ =
        gn21ScaledStateEarning μ arrivalRate w σ -
          g * gn21ScaledStateTime μ arrivalRate σ -
            d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
              (g + d * switchIJ) := by
    calc
      arrivalRate *
          ∫ τ in σ, w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ ∂μ =
        gn21ScaledStateEarning μ arrivalRate w σ -
          g * gn21ScaledStateTime μ arrivalRate σ -
            d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
              g + d * switchIJ := hsurplus
      _ = gn21ScaledStateEarning μ arrivalRate w σ -
          g * gn21ScaledStateTime μ arrivalRate σ -
            d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
              (g + d * switchIJ) := by ring
  rw [hconstant] at hsurplus'
  linarith

/-- A pointwise Bellman envelope bounds a state's scaled earning for every
feasible policy.  The accept-all accounting equality fixes the constant term
in the envelope. -/
theorem gn21ScaledStateEarning_le_bellman_envelope
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI g d : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        acceptAllPolicy μ)
    (hw_integrable : IntegrableOn w acceptAllPolicy μ)
    (haccept_all_accounting :
      gn21ScaledStateEarning μ arrivalRate w acceptAllPolicy =
        g * gn21ScaledStateTime μ arrivalRate acceptAllPolicy +
          d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI
            acceptAllPolicy)
    (henvelope : ∀ τ : TripLength, 0 < τ →
      0 ≤ w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ) :
    gn21ScaledStateEarning μ arrivalRate w σ ≤
      g * gn21ScaledStateTime μ arrivalRate σ +
        d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  let advantage : TripLength → ℝ := fun τ =>
    w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ
  have hadvantage_integrable : IntegrableOn advantage acceptAllPolicy μ := by
    dsimp [advantage]
    convert hw_integrable.sub
      ((htime_integrable.const_mul g).add (hq_integrable.const_mul d)) using 1
    ext τ
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hadvantage_nonneg : 0 ≤ᵐ[μ.restrict acceptAllPolicy] advantage :=
    (ae_restrict_iff' measurableSet_acceptAllPolicy).2
      (Filter.Eventually.of_forall fun τ hτ => henvelope τ hτ)
  have hmono :
      ∫ τ in σ, advantage τ ∂μ ≤ ∫ τ in acceptAllPolicy, advantage τ ∂μ :=
    setIntegral_mono_set hadvantage_integrable hadvantage_nonneg
      (Filter.Eventually.of_forall hσ_subset)
  have htime_sigma := htime_integrable.mono_set hσ_subset
  have hq_sigma := hq_integrable.mono_set hσ_subset
  have hw_sigma := hw_integrable.mono_set hσ_subset
  have hadvantage_integral_sigma :
      ∫ τ in σ, advantage τ ∂μ =
        ∫ τ in σ, w τ ∂μ - g * ∫ τ in σ, τ ∂μ -
          d * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
    calc
      ∫ τ in σ, advantage τ ∂μ =
          ∫ τ in σ,
            (w τ - g * τ) - d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rfl
      _ = ∫ τ in σ, w τ - g * τ ∂μ -
            ∫ τ in σ, d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              simpa only [Pi.sub_apply] using
                (integral_sub (hw_sigma.sub (htime_sigma.const_mul g))
                  (hq_sigma.const_mul d))
      _ = (∫ τ in σ, w τ ∂μ - ∫ τ in σ, g * τ ∂μ) -
            ∫ τ in σ, d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_sub hw_sigma (htime_sigma.const_mul g)]
      _ = ∫ τ in σ, w τ ∂μ - g * ∫ τ in σ, τ ∂μ -
            d * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_const_mul, integral_const_mul]
  have hcurrent_eq :
      arrivalRate * ∫ τ in σ, advantage τ ∂μ =
        gn21ScaledStateEarning μ arrivalRate w σ -
          g * gn21ScaledStateTime μ arrivalRate σ -
            d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
              g + d * switchIJ := by
    rw [hadvantage_integral_sigma]
    unfold gn21ScaledStateEarning gn21ScaledStateTime gn21ExitWeightIntegral
      singleStateTripPayment singleStateTripTime
    ring
  have hadvantage_integral_all :
      ∫ τ in acceptAllPolicy, advantage τ ∂μ =
        ∫ τ in acceptAllPolicy, w τ ∂μ -
          g * ∫ τ in acceptAllPolicy, τ ∂μ -
          d * ∫ τ in acceptAllPolicy,
            gn21SwitchProb switchIJ switchJI τ ∂μ := by
    calc
      ∫ τ in acceptAllPolicy, advantage τ ∂μ =
          ∫ τ in acceptAllPolicy,
            (w τ - g * τ) - d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rfl
      _ = ∫ τ in acceptAllPolicy, w τ - g * τ ∂μ -
            ∫ τ in acceptAllPolicy, d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              simpa only [Pi.sub_apply] using
                (integral_sub (hw_integrable.sub (htime_integrable.const_mul g))
                  (hq_integrable.const_mul d))
      _ = (∫ τ in acceptAllPolicy, w τ ∂μ -
              ∫ τ in acceptAllPolicy, g * τ ∂μ) -
            ∫ τ in acceptAllPolicy,
              d * gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_sub hw_integrable (htime_integrable.const_mul g)]
      _ = ∫ τ in acceptAllPolicy, w τ ∂μ -
            g * ∫ τ in acceptAllPolicy, τ ∂μ -
            d * ∫ τ in acceptAllPolicy,
              gn21SwitchProb switchIJ switchJI τ ∂μ := by
              rw [integral_const_mul, integral_const_mul]
  have hall_eq :
      arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ =
        g + d * switchIJ := by
    calc
      arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ =
          gn21ScaledStateEarning μ arrivalRate w acceptAllPolicy -
            g * gn21ScaledStateTime μ arrivalRate acceptAllPolicy -
              d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI
                acceptAllPolicy + g + d * switchIJ := by
              rw [hadvantage_integral_all]
              unfold gn21ScaledStateEarning gn21ScaledStateTime
                gn21ExitWeightIntegral singleStateTripPayment singleStateTripTime
              ring
      _ = g + d * switchIJ := by
              rw [haccept_all_accounting]
              ring
  have hscaled_mono :
      arrivalRate * ∫ τ in σ, advantage τ ∂μ ≤
        arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ :=
    mul_le_mul_of_nonneg_left hmono harrival_nonneg
  rw [hcurrent_eq, hall_eq] at hscaled_mono
  linarith

/-- A strictly positive Bellman advantage makes every positive-measure
omission from accept-all strictly worse in that state. -/
theorem gn21ScaledStateEarning_lt_bellman_envelope_of_rejected_measure_pos
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI g d : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        acceptAllPolicy μ)
    (hw_integrable : IntegrableOn w acceptAllPolicy μ)
    (haccept_all_accounting :
      gn21ScaledStateEarning μ arrivalRate w acceptAllPolicy =
        g * gn21ScaledStateTime μ arrivalRate acceptAllPolicy +
          d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI
            acceptAllPolicy)
    (henvelope : ∀ τ : TripLength, 0 < τ →
      0 < w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ)
    (hrejected_pos : 0 < μ (acceptAllPolicy \ σ)) :
    gn21ScaledStateEarning μ arrivalRate w σ <
      g * gn21ScaledStateTime μ arrivalRate σ +
        d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  let advantage : TripLength → ℝ := fun τ =>
    w τ - g * τ - d * gn21SwitchProb switchIJ switchJI τ
  have hadvantage_integrable : IntegrableOn advantage acceptAllPolicy μ := by
    dsimp [advantage]
    convert hw_integrable.sub
      ((htime_integrable.const_mul g).add (hq_integrable.const_mul d)) using 1
    ext τ
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have htime_sigma := htime_integrable.mono_set hσ_subset
  have hq_sigma := hq_integrable.mono_set hσ_subset
  have hw_sigma := hw_integrable.mono_set hσ_subset
  have hcomp_measurable : MeasurableSet (acceptAllPolicy \ σ) :=
    measurableSet_acceptAllPolicy.diff hσ_measurable
  have hcomp_subset : acceptAllPolicy \ σ ⊆ acceptAllPolicy := Set.diff_subset
  have hcomp_integrable := hadvantage_integrable.mono_set hcomp_subset
  have hcomp_nonneg : 0 ≤ᵐ[μ.restrict (acceptAllPolicy \ σ)] advantage :=
    (ae_restrict_iff' hcomp_measurable).2
      (Filter.Eventually.of_forall fun τ hτ =>
        le_of_lt (henvelope τ hτ.1))
  have hsupport : Function.support advantage ∩ (acceptAllPolicy \ σ) =
      acceptAllPolicy \ σ := by
    ext τ
    constructor
    · exact fun hτ => hτ.2
    · intro hτ
      exact ⟨ne_of_gt (henvelope τ hτ.1), hτ⟩
  have hcomp_integral_pos :
      0 < ∫ τ in acceptAllPolicy \ σ, advantage τ ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae hcomp_nonneg hcomp_integrable).2
      (by simpa [hsupport] using hrejected_pos)
  have hmono_lt :
      ∫ τ in σ, advantage τ ∂μ <
        ∫ τ in acceptAllPolicy, advantage τ ∂μ := by
    have hdiff := setIntegral_diff hσ_measurable hadvantage_integrable hσ_subset
    linarith
  have hscaled_mono_lt :
      arrivalRate * ∫ τ in σ, advantage τ ∂μ <
        arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ :=
    mul_lt_mul_of_pos_left hmono_lt harrival_pos
  have hcurrent_eq :
      arrivalRate * ∫ τ in σ, advantage τ ∂μ =
        gn21ScaledStateEarning μ arrivalRate w σ -
          g * gn21ScaledStateTime μ arrivalRate σ -
            d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ +
              g + d * switchIJ := by
    simpa [advantage] using
      (gn21ScaledStateEarning_bellman_surplus_eq μ arrivalRate switchIJ
        switchJI g d w σ htime_sigma hq_sigma hw_sigma)
  have hall_eq :
      arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ =
        g + d * switchIJ := by
    calc
      arrivalRate * ∫ τ in acceptAllPolicy, advantage τ ∂μ =
          gn21ScaledStateEarning μ arrivalRate w acceptAllPolicy -
            g * gn21ScaledStateTime μ arrivalRate acceptAllPolicy -
              d * gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI
                acceptAllPolicy + g + d * switchIJ := by
              simpa [advantage] using
                (gn21ScaledStateEarning_bellman_surplus_eq μ arrivalRate
                  switchIJ switchJI g d w acceptAllPolicy htime_integrable
                  hq_integrable hw_integrable)
      _ = g + d * switchIJ := by
              rw [haccept_all_accounting]
              ring
  rw [hcurrent_eq, hall_eq] at hscaled_mono_lt
  linarith

/-- Statewise Bellman envelopes combine directly into an upper bound on the
Appendix-D aggregate reward. -/
theorem gn21AggregateDynamicReward_le_of_bellman_envelopes
    (Q0 Q1 T0 T1 W0 W1 g d0 d1 : ℝ)
    (hQ0_pos : 0 < Q0) (hQ1_pos : 0 < Q1)
    (hT0_pos : 0 < T0) (hT1_pos : 0 < T1)
    (hW0 : W0 ≤ g * T0 + d0 * Q0)
    (hW1 : W1 ≤ g * T1 + d1 * Q1)
    (hd : d0 + d1 = 0) :
    gn21AggregateDynamicReward Q0 Q1 T0 T1 W0 W1 ≤ g := by
  have hden_pos : 0 < Q0 * T1 + Q1 * T0 :=
    gn21AggregateDenominator_pos_of_pos Q0 Q1 T0 T1
      hQ0_pos hQ1_pos hT0_pos hT1_pos
  have hleft : Q1 * W0 ≤ Q1 * (g * T0 + d0 * Q0) :=
    mul_le_mul_of_nonneg_left hW0 (le_of_lt hQ1_pos)
  have hright : Q0 * W1 ≤ Q0 * (g * T1 + d1 * Q1) :=
    mul_le_mul_of_nonneg_left hW1 (le_of_lt hQ0_pos)
  unfold gn21AggregateDynamicReward
  rw [div_le_iff₀ hden_pos]
  calc
    Q0 * W1 + Q1 * W0 ≤
        Q0 * (g * T1 + d1 * Q1) + Q1 * (g * T0 + d0 * Q0) :=
      add_le_add hright hleft
    _ = g * (Q0 * T1 + Q1 * T0) + Q0 * Q1 * (d0 + d1) := by
      ring
    _ = g * (Q0 * T1 + Q1 * T0) := by rw [hd]; ring

/-- A strict left-state Bellman envelope makes the aggregate reward strictly
smaller. -/
theorem gn21AggregateDynamicReward_lt_of_bellman_envelopes_left
    (Q0 Q1 T0 T1 W0 W1 g d0 d1 : ℝ)
    (hQ0_pos : 0 < Q0) (hQ1_pos : 0 < Q1)
    (hT0_pos : 0 < T0) (hT1_pos : 0 < T1)
    (hW0 : W0 < g * T0 + d0 * Q0)
    (hW1 : W1 ≤ g * T1 + d1 * Q1)
    (hd : d0 + d1 = 0) :
    gn21AggregateDynamicReward Q0 Q1 T0 T1 W0 W1 < g := by
  have hden_pos : 0 < Q0 * T1 + Q1 * T0 :=
    gn21AggregateDenominator_pos_of_pos Q0 Q1 T0 T1
      hQ0_pos hQ1_pos hT0_pos hT1_pos
  have hleft : Q1 * W0 < Q1 * (g * T0 + d0 * Q0) :=
    mul_lt_mul_of_pos_left hW0 hQ1_pos
  have hright : Q0 * W1 ≤ Q0 * (g * T1 + d1 * Q1) :=
    mul_le_mul_of_nonneg_left hW1 (le_of_lt hQ0_pos)
  unfold gn21AggregateDynamicReward
  rw [div_lt_iff₀ hden_pos]
  calc
    Q0 * W1 + Q1 * W0 <
        Q0 * (g * T1 + d1 * Q1) + Q1 * (g * T0 + d0 * Q0) :=
      add_lt_add_of_le_of_lt hright hleft
    _ = g * (Q0 * T1 + Q1 * T0) + Q0 * Q1 * (d0 + d1) := by
      ring
    _ = g * (Q0 * T1 + Q1 * T0) := by rw [hd]; ring

/-- A strict right-state Bellman envelope makes the aggregate reward strictly
smaller. -/
theorem gn21AggregateDynamicReward_lt_of_bellman_envelopes_right
    (Q0 Q1 T0 T1 W0 W1 g d0 d1 : ℝ)
    (hQ0_pos : 0 < Q0) (hQ1_pos : 0 < Q1)
    (hT0_pos : 0 < T0) (hT1_pos : 0 < T1)
    (hW0 : W0 ≤ g * T0 + d0 * Q0)
    (hW1 : W1 < g * T1 + d1 * Q1)
    (hd : d0 + d1 = 0) :
    gn21AggregateDynamicReward Q0 Q1 T0 T1 W0 W1 < g := by
  have hden_pos : 0 < Q0 * T1 + Q1 * T0 :=
    gn21AggregateDenominator_pos_of_pos Q0 Q1 T0 T1
      hQ0_pos hQ1_pos hT0_pos hT1_pos
  have hleft : Q1 * W0 ≤ Q1 * (g * T0 + d0 * Q0) :=
    mul_le_mul_of_nonneg_left hW0 (le_of_lt hQ1_pos)
  have hright : Q0 * W1 < Q0 * (g * T1 + d1 * Q1) :=
    mul_lt_mul_of_pos_left hW1 hQ0_pos
  unfold gn21AggregateDynamicReward
  rw [div_lt_iff₀ hden_pos]
  calc
    Q0 * W1 + Q1 * W0 <
        Q0 * (g * T1 + d1 * Q1) + Q1 * (g * T0 + d0 * Q0) :=
      add_lt_add_of_lt_of_le hright hleft
    _ = g * (Q0 * T1 + Q1 * T0) + Q0 * Q1 * (d0 + d1) := by
      ring
    _ = g * (Q0 * T1 + Q1 * T0) := by rw [hd]; ring

/--
Direct verification of the accept-all branch of GN21 Theorem 3.  The price
coefficients are selected once from the accept-all primitives.  Their Bellman
advantages then bound the Appendix-D aggregate reward for every open
deviation, so this does not use a per-policy interval as a fixed-price
certificate.  The proof accepts either the printed sufficient threshold or
the weaker Bellman threshold which is the condition it actually uses.
-/
theorem gn21_theorem3_structured_open_ic_of_source_or_bellman_primitives
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (hR2_pos : 0 < R2)
    (hsource_or_bellman :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < R1 / R2 ∨
        gn21AcceptAllScaledStateTime (mu 1) (arrival 1) *
            (switch12 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
              gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
                switch12 switch21) /
            (gn21AcceptAllScaledStateTime (mu 0) (arrival 0) *
              (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12 +
                switch12 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1))) <
          R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
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
            dynamicAcceptAllAlmostEverywhere mu rho := by
  let rho : ℝ := R1 / R2
  let T0 : ℝ := gn21AcceptAllScaledStateTime (mu 0) (arrival 0)
  let T1 : ℝ := gn21AcceptAllScaledStateTime (mu 1) (arrival 1)
  let Q0 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
  let Q1 : ℝ :=
    gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
  have hrho_lt_one : rho < 1 := by
    simpa [rho] using hratio_lt_one
  have hR1_eq : R1 = rho * R2 := by
    dsimp [rho]
    field_simp [ne_of_gt hR2_pos]
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
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
  have hbellman_ratio :
      T1 * (switch12 * T0 - Q0) /
          (T0 * (Q1 + switch12 * T1)) < rho := by
    rcases hsource_or_bellman with hsource | hbellman
    · apply theorem3_bellman_nonsurge_threshold_lt_of_source_ratio
        T0 T1 Q0 Q1 switch12 rho
      · simpa [T0, T1, Q0, Q1, rho] using hsource
      · exact hT0_pos
      · exact hT1_pos
      · exact hQ0_pos
      · exact hQ1_pos
      · exact hswitch12_pos
      · exact hgap0_pos
    · simpa [T0, T1, Q0, Q1, rho] using hbellman
  have hbellman_den_pos : 0 < T0 * (Q1 + switch12 * T1) := by
    exact mul_pos hT0_pos (add_pos hQ1_pos (mul_pos hswitch12_pos hT1_pos))
  have hbellman_threshold_pos :
      0 < T1 * (switch12 * T0 - Q0) /
          (T0 * (Q1 + switch12 * T1)) :=
    div_pos (mul_pos hT1_pos hgap0_pos) hbellman_den_pos
  have hrho_pos : 0 < rho :=
    lt_trans hbellman_threshold_pos hbellman_ratio
  have hR1_pos : 0 < R1 := by
    rw [hR1_eq]
    exact mul_pos hrho_pos hR2_pos
  have hR1_lt_R2 : R1 < R2 := by
    calc
      R1 = rho * R2 := hR1_eq
      _ < 1 * R2 := mul_lt_mul_of_pos_right hrho_lt_one hR2_pos
      _ = R2 := by ring
  let D : ℝ := Q0 * T1 + Q1 * T0
  have hD_pos : 0 < D := by
    dsimp [D]
    exact add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let g : ℝ := (Q0 * R2 * T1 + Q1 * R1 * T0) / D
  let d0 : ℝ := (R1 - g) * T0 / Q0
  let d1 : ℝ := -d0
  have hg_pos : 0 < g := by
    dsimp [g]
    apply div_pos
    · exact add_pos (mul_pos (mul_pos hQ0_pos hR2_pos) hT1_pos)
        (mul_pos (mul_pos hQ1_pos hR1_pos) hT0_pos)
    · exact hD_pos
  have hg_gt_R1 : R1 < g := by
    dsimp [g, D]
    rw [lt_div_iff₀ hD_pos]
    have hgap : 0 < Q0 * T1 * (R2 - R1) :=
      mul_pos (mul_pos hQ0_pos hT1_pos) (sub_pos.mpr hR1_lt_R2)
    nlinarith
  have hd1_nonneg : 0 ≤ d1 := by
    have hd1_eq : d1 = (g - R1) * T0 / Q0 := by
      dsimp [d1, d0]
      ring
    rw [hd1_eq]
    exact le_of_lt (div_pos (mul_pos (sub_pos.mpr hg_gt_R1) hT0_pos) hQ0_pos)
  have hd_sum : d0 + d1 = 0 := by
    dsimp [d1]
    ring
  have hstate0 : R1 * T0 = g * T0 + d0 * Q0 := by
    dsimp [d0]
    field_simp [ne_of_gt hQ0_pos]
    ring
  have hstate1 : R2 * T1 = g * T1 + d1 * Q1 := by
    dsimp [g, d0, d1, D]
    field_simp [ne_of_gt hQ0_pos, ne_of_gt hD_pos]
    ring
  have hbellman_cross :
      T1 * (switch12 * T0 - Q0) <
        rho * (T0 * (Q1 + switch12 * T1)) := by
    exact (div_lt_iff₀ hbellman_den_pos).mp hbellman_ratio
  have hbellman_bracket_pos :
      0 < rho * T0 * (Q1 + switch12 * T1) -
        T1 * (switch12 * T0 - Q0) := by
    nlinarith
  have hslack0 : 0 < g + d0 * switch12 := by
    have hformula :
        g + d0 * switch12 =
          R2 / D *
            (rho * T0 * (Q1 + switch12 * T1) -
              T1 * (switch12 * T0 - Q0)) := by
      dsimp [g, d0, D, rho]
      field_simp [ne_of_gt hQ0_pos, ne_of_gt hD_pos, ne_of_gt hR2_pos]
      ring
    rw [hformula]
    exact mul_pos (div_pos hR2_pos hD_pos) hbellman_bracket_pos
  have hslack1 : 0 < g + d1 * switch21 := by
    exact add_pos_of_pos_of_nonneg hg_pos
      (mul_nonneg hd1_nonneg (le_of_lt hswitch21_pos))
  rcases gn21BellmanStructuredParameters_exist
      T0 T1 Q0 Q1 R1 R2 switch12 switch21 g d0 d1
      hT0_sub_one_pos hT1_sub_one_pos hQ0_sub_switch_pos hQ1_sub_switch_pos
      hg_pos hd1_nonneg hstate0 hstate1 hslack0 hslack1 with
    ⟨m0, m1, z0, z1, hm0_pos, hm1_pos, hz1_nonneg,
      haccount0, haccount1, hmg0_pos, hzd0_pos, hmg1_pos, hzd1_pos⟩
  let m : Fin 2 → ℝ := fun i => if i = 0 then m0 else m1
  let z : Fin 2 → ℝ := fun i => if i = 0 then z0 else z1
  have hm0 : m 0 = m0 := by simp [m]
  have hm1 : m 1 = m1 := by simp [m]
  have hz0 : z 0 = z0 := by simp [z]
  have hz1 : z 1 = z1 := by simp [z]
  have hW0_target :
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        R1 * gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy := by
    calc
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        m0 * (T0 - 1) + z0 * (Q0 - switch12) := by
          simpa [T0, Q0, ctmcStructuredDynamicSurgePrice,
            ctmcDynamicSwitchProb, m, z] using
            (paper_remark2_structured_scaled_earning_algebra
              (mu 0) (arrival 0) m0 z0 switch12 switch21 acceptAllPolicy
              htime1_integrable hq0_integrable)
      _ = R1 * gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy := by
        simpa [T0, Q0] using haccount0
  have hW1_target :
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        R2 * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy := by
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
      _ = R2 * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy := by
        simpa [T1, Q1] using haccount1
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
      _ = R1 * gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy :=
        hW0_target
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
      _ = R2 * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy :=
        hW1_target
  have haccounting0 :
      gn21ScaledStateEarning (mu 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        g * gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy +
          d0 * gn21ExitWeightIntegral (mu 0) (arrival 0)
            switch12 switch21 acceptAllPolicy := by
    rw [hW0_target]
    simpa [T0, Q0] using hstate0
  have haccounting1 :
      gn21ScaledStateEarning (mu 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        g * gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy +
          d1 * gn21ExitWeightIntegral (mu 1) (arrival 1)
            switch21 switch12 acceptAllPolicy := by
    rw [hW1_target]
    simpa [T1, Q1] using hstate1
  have henvelope0 : ∀ tau : TripLength, 0 < tau →
      0 < ctmcStructuredDynamicSurgePrice m z switch12 switch21 0 tau -
        g * tau - d0 * gn21SwitchProb switch12 switch21 tau := by
    intro tau htau
    have hq_nonneg : 0 ≤ gn21SwitchProb switch12 switch21 tau :=
      paper_lemma2_switch_probability_nonneg switch12 switch21 tau
        (le_of_lt hswitch12_pos) hsum12 (le_of_lt htau)
    have htime_term : 0 < (m0 - g) * tau := mul_pos hmg0_pos htau
    have hq_term : 0 ≤ (z0 - d0) * gn21SwitchProb switch12 switch21 tau :=
      mul_nonneg (le_of_lt hzd0_pos) hq_nonneg
    calc
      0 < (m0 - g) * tau +
          (z0 - d0) * gn21SwitchProb switch12 switch21 tau :=
        add_pos_of_pos_of_nonneg htime_term hq_term
      _ = ctmcStructuredDynamicSurgePrice m z switch12 switch21 0 tau -
          g * tau - d0 * gn21SwitchProb switch12 switch21 tau := by
        simp [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          structuredSurgePrice, m, z]
        ring
  have henvelope1 : ∀ tau : TripLength, 0 < tau →
      0 < ctmcStructuredDynamicSurgePrice m z switch12 switch21 1 tau -
        g * tau - d1 * gn21SwitchProb switch21 switch12 tau := by
    intro tau htau
    have hq_nonneg : 0 ≤ gn21SwitchProb switch21 switch12 tau :=
      paper_lemma2_switch_probability_nonneg switch21 switch12 tau
        (le_of_lt hswitch21_pos) hsum21 (le_of_lt htau)
    have htime_term : 0 < (m1 - g) * tau := mul_pos hmg1_pos htau
    have hq_term : 0 ≤ (z1 - d1) * gn21SwitchProb switch21 switch12 tau :=
      mul_nonneg (le_of_lt hzd1_pos) hq_nonneg
    calc
      0 < (m1 - g) * tau +
          (z1 - d1) * gn21SwitchProb switch21 switch12 tau :=
        add_pos_of_pos_of_nonneg htime_term hq_term
      _ = ctmcStructuredDynamicSurgePrice m z switch12 switch21 1 tau -
          g * tau - d1 * gn21SwitchProb switch21 switch12 tau := by
        simp [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          structuredSurgePrice, m, z]
        ring
  have haggregate_acceptAll :
      gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
        acceptAllDynamicPolicy = g := by
    have haggregate :
        gn21AggregateDynamicReward Q0 Q1 T0 T1 (R1 * T0) (R2 * T1) = g := by
      unfold gn21AggregateDynamicReward
      dsimp [g, D]
      field_simp [ne_of_gt hD_pos]
    change
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            acceptAllPolicy)
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (mu 0) (arrival 0) acceptAllPolicy)
          (gn21ScaledStateTime (mu 1) (arrival 1) acceptAllPolicy)
          (gn21ScaledStateEarning (mu 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy)
          (gn21ScaledStateEarning (mu 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy) = g
    rw [hW0_target, hW1_target]
    simpa [T0, T1, Q0, Q1] using haggregate
  have hopen : dynamicOpenOptimal
      (gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z)
      acceptAllDynamicPolicy := by
    refine ⟨dynamicFeasibleOpenPolicy_acceptAllDynamicPolicy, ?_⟩
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
    have hW0_bound : W0s ≤ g * T0s + d0 * Q0s := by
      dsimp [W0s, T0s, Q0s]
      exact gn21ScaledStateEarning_le_bellman_envelope
        (mu 0) (arrival 0) switch12 switch21 g d0
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0)
        (le_of_lt harrival1_pos) (hsigma 0).1
        htime1_integrable hq0_integrable hw0_integrable haccounting0
        (fun tau htau => le_of_lt (henvelope0 tau htau))
    have hW1_bound : W1s ≤ g * T1s + d1 * Q1s := by
      dsimp [W1s, T1s, Q1s]
      exact gn21ScaledStateEarning_le_bellman_envelope
        (mu 1) (arrival 1) switch21 switch12 g d1
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)
        (le_of_lt harrival2_pos) (hsigma 1).1
        htime2_integrable hq1_integrable hw1_integrable haccounting1
        (fun tau htau => le_of_lt (henvelope1 tau htau))
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
        hQ0s_pos hQ1s_pos hT0s_pos hT1s_pos hW0_bound hW1_bound hd_sum
    change
      gn21AggregateDynamicReward Q0s Q1s T0s T1s W0s W1s ≤
        gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
          acceptAllDynamicPolicy
    rw [haggregate_acceptAll]
    exact haggregate
  have hunique : ∀ sigma : Fin 2 → TripPolicy,
      dynamicOpenOptimal
        (gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z)
        sigma → dynamicAcceptAllAlmostEverywhere mu sigma := by
    intro sigma hsigma i
    fin_cases i
    · unfold acceptAllAlmostEverywhere
      by_contra hzero
      have hrejected_pos : 0 < (mu 0) (acceptAllPolicy \ sigma 0) :=
        pos_iff_ne_zero.mpr hzero
      have hsigma0_meas : MeasurableSet (sigma 0) := (hsigma.1 0).2.measurableSet
      have hsigma1_meas : MeasurableSet (sigma 1) := (hsigma.1 1).2.measurableSet
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
      have hW0_strict :
          gn21ScaledStateEarning (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (sigma 0) <
            g * gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0) +
              d0 * gn21ExitWeightIntegral (mu 0) (arrival 0)
                switch12 switch21 (sigma 0) :=
        gn21ScaledStateEarning_lt_bellman_envelope_of_rejected_measure_pos
          (mu 0) (arrival 0) switch12 switch21 g d0
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0)
          harrival1_pos (hsigma.1 0).1 hsigma0_meas
          htime1_integrable hq0_integrable hw0_integrable haccounting0
          henvelope0 hrejected_pos
      have hW1_bound :
          gn21ScaledStateEarning (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              (sigma 1) ≤
            g * gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1) +
              d1 * gn21ExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12 (sigma 1) :=
        gn21ScaledStateEarning_le_bellman_envelope
          (mu 1) (arrival 1) switch21 switch12 g d1
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)
          (le_of_lt harrival2_pos) (hsigma.1 1).1
          htime2_integrable hq1_integrable hw1_integrable haccounting1
          (fun tau htau => le_of_lt (henvelope1 tau htau))
      have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0) :=
        gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (sigma 0)
          (le_of_lt harrival1_pos) hsigma0_meas (hsigma.1 0).1
      have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1) :=
        gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (sigma 1)
          (le_of_lt harrival2_pos) hsigma1_meas (hsigma.1 1).1
      have hQ0_pos :
          0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (sigma 0) :=
        gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
          switch12 switch21 (sigma 0) (le_of_lt harrival1_pos)
          hswitch12_pos hsum12 hsigma0_meas (hsigma.1 0).1
      have hQ1_pos :
          0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (sigma 1) :=
        gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
          switch21 switch12 (sigma 1) (le_of_lt harrival2_pos)
          hswitch21_pos hsum21 hsigma1_meas (hsigma.1 1).1
      have hstrict :
          gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              sigma < g := by
        change gn21AggregateDynamicReward
            (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (sigma 0))
            (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (sigma 1))
            (gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0))
            (gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1))
            (gn21ScaledStateEarning (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0))
            (gn21ScaledStateEarning (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)) < g
        exact gn21AggregateDynamicReward_lt_of_bellman_envelopes_left
          _ _ _ _ _ _ g d0 d1 hQ0_pos hQ1_pos hT0_pos hT1_pos
          hW0_strict hW1_bound hd_sum
      have hoptimal :
          gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              acceptAllDynamicPolicy ≤
            gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              sigma :=
        hsigma.2 acceptAllDynamicPolicy dynamicFeasibleOpenPolicy_acceptAllDynamicPolicy
      rw [haggregate_acceptAll] at hoptimal
      linarith
    · unfold acceptAllAlmostEverywhere
      by_contra hzero
      have hrejected_pos : 0 < (mu 1) (acceptAllPolicy \ sigma 1) :=
        pos_iff_ne_zero.mpr hzero
      have hsigma0_meas : MeasurableSet (sigma 0) := (hsigma.1 0).2.measurableSet
      have hsigma1_meas : MeasurableSet (sigma 1) := (hsigma.1 1).2.measurableSet
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
      have hW0_bound :
          gn21ScaledStateEarning (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (sigma 0) ≤
            g * gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0) +
              d0 * gn21ExitWeightIntegral (mu 0) (arrival 0)
                switch12 switch21 (sigma 0) :=
        gn21ScaledStateEarning_le_bellman_envelope
          (mu 0) (arrival 0) switch12 switch21 g d0
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0)
          (le_of_lt harrival1_pos) (hsigma.1 0).1
          htime1_integrable hq0_integrable hw0_integrable haccounting0
          (fun tau htau => le_of_lt (henvelope0 tau htau))
      have hW1_strict :
          gn21ScaledStateEarning (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              (sigma 1) <
            g * gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1) +
              d1 * gn21ExitWeightIntegral (mu 1) (arrival 1)
                switch21 switch12 (sigma 1) :=
        gn21ScaledStateEarning_lt_bellman_envelope_of_rejected_measure_pos
          (mu 1) (arrival 1) switch21 switch12 g d1
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)
          harrival2_pos (hsigma.1 1).1 hsigma1_meas
          htime2_integrable hq1_integrable hw1_integrable haccounting1
          henvelope1 hrejected_pos
      have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0) :=
        gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (sigma 0)
          (le_of_lt harrival1_pos) hsigma0_meas (hsigma.1 0).1
      have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1) :=
        gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (sigma 1)
          (le_of_lt harrival2_pos) hsigma1_meas (hsigma.1 1).1
      have hQ0_pos :
          0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (sigma 0) :=
        gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
          switch12 switch21 (sigma 0) (le_of_lt harrival1_pos)
          hswitch12_pos hsum12 hsigma0_meas (hsigma.1 0).1
      have hQ1_pos :
          0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (sigma 1) :=
        gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
          switch21 switch12 (sigma 1) (le_of_lt harrival2_pos)
          hswitch21_pos hsum21 hsigma1_meas (hsigma.1 1).1
      have hstrict :
          gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              sigma < g := by
        change gn21AggregateDynamicReward
            (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (sigma 0))
            (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (sigma 1))
            (gn21ScaledStateTime (mu 0) (arrival 0) (sigma 0))
            (gn21ScaledStateTime (mu 1) (arrival 1) (sigma 1))
            (gn21ScaledStateEarning (mu 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (sigma 0))
            (gn21ScaledStateEarning (mu 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (sigma 1)) < g
        exact gn21AggregateDynamicReward_lt_of_bellman_envelopes_right
          _ _ _ _ _ _ g d0 d1 hQ0_pos hQ1_pos hT0_pos hT1_pos
          hW0_bound hW1_strict hd_sum
      have hoptimal :
          gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              acceptAllDynamicPolicy ≤
            gn21AggregateCTMCStructuredDynamicReward mu arrival switch12 switch21 m z
              sigma :=
        hsigma.2 acceptAllDynamicPolicy dynamicFeasibleOpenPolicy_acceptAllDynamicPolicy
      rw [haggregate_acceptAll] at hoptimal
      linarith
  exact ⟨m, z, ⟨le_of_lt hm0_pos, le_of_lt hm1_pos, hz1_nonneg⟩,
    hrate0, hrate1, hopen, hunique⟩

/--
The accept-all branch under the Bellman threshold actually used by the direct
verification.  This covers the interval between the endpoint construction and
the paper's displayed sufficient threshold.
-/
theorem gn21_theorem3_structured_open_ic_of_bellman_primitives
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (hR2_pos : 0 < R2)
    (hbellman_lt_ratio :
      gn21AcceptAllScaledStateTime (mu 1) (arrival 1) *
          (switch12 * gn21AcceptAllScaledStateTime (mu 0) (arrival 0) -
            gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0)
              switch12 switch21) /
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0) *
            (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1)
              switch21 switch12 +
              switch12 * gn21AcceptAllScaledStateTime (mu 1) (arrival 1))) <
        R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
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
            dynamicAcceptAllAlmostEverywhere mu rho := by
  exact gn21_theorem3_structured_open_ic_of_source_or_bellman_primitives
    mu arrival R1 R2 switch12 switch21 hR2_pos (Or.inr hbellman_lt_ratio)
    hratio_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one

/--
The paper's displayed `C < R1 / R2` condition is a sufficient route into the
direct Bellman verification.
-/
theorem gn21_theorem3_structured_open_ic_of_source_primitives
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (hR2_pos : 0 < R2)
    (hC_lt_ratio :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch12 < R1 / R2)
    (hratio_lt_one : R1 / R2 < 1)
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
            dynamicAcceptAllAlmostEverywhere mu rho := by
  exact gn21_theorem3_structured_open_ic_of_source_or_bellman_primitives
    mu arrival R1 R2 switch12 switch21 hR2_pos (Or.inl hC_lt_ratio)
    hratio_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one

end

end GN21DriverSurgePricing
