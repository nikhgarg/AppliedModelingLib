import GN21DriverSurgePricing.DomainBridge

/-!
# Direct fixed-marginal comparisons for GN21 Theorem 4

These are generic Appendix-D quotient calculations.  They belong below the
affine response analysis so that a fixed-marginal affine theorem can use the
actual open-optimum comparison without importing the Theorem 4 attainment
assembly.
-/

open AppliedModelingLib
open MeasureTheory

namespace GN21DriverSurgePricing

/--
State-swapped aggregate-to-marginal bridge for a right-coordinate update.
This is stated directly for the Appendix-D aggregate functional and contains
no endpoint or policy-form assumption.
-/
theorem gn21MeasuredRightMarginalSetReward_candidate_le_of_aggregate_update_le_direct
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicFeasibleMeasurablePolicy rho)
    (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_measurable : MeasurableSet candidate)
    (hupdate :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1 candidate) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho) :
    lemma5MarginalSetReward (mu 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        candidate <=
      lemma5MarginalSetReward (mu 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (rho 1) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hrho0_subset : rho 0 ⊆ acceptAllPolicy := (hrho 0).1
  have hrho0_measurable : MeasurableSet (rho 0) := (hrho 0).2
  have hrho1_subset : rho 1 ⊆ acceptAllPolicy := (hrho 1).1
  have hrho1_measurable : MeasurableSet (rho 1) := (hrho 1).2
  have hq_candidate :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        candidate (mu 1) :=
    hq1.mono_set hcandidate_subset
  have hq_current :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        (rho 1) (mu 1) :=
    hq1.mono_set hrho1_subset
  have hw_candidate : IntegrableOn (w 1) candidate (mu 1) :=
    hw1.mono_set hcandidate_subset
  have hw_current : IntegrableOn (w 1) (rho 1) (mu 1) :=
    hw1.mono_set hrho1_subset
  have htime_candidate : IntegrableOn (fun tau : TripLength => tau) candidate (mu 1) :=
    htime1.mono_set hcandidate_subset
  have htime_current : IntegrableOn (fun tau : TripLength => tau) (rho 1) (mu 1) :=
    htime1.mono_set hrho1_subset
  have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (rho 0)
      (le_of_lt harrival0_pos) hrho0_measurable hrho0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (rho 1)
      (le_of_lt harrival1_pos) hrho1_measurable hrho1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
      switch21 (rho 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hrho0_measurable hrho0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
      switch12 (rho 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hrho1_measurable hrho1_subset
  have hT1'_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) candidate :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) candidate
      (le_of_lt harrival1_pos) hcandidate_measurable hcandidate_subset
  have hQ1'_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 candidate :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
      switch12 candidate (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hcandidate_measurable hcandidate_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hden'_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) candidate +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 candidate *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1'_pos) (mul_pos hQ1'_pos hT0_pos)
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 candidate)
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ScaledStateTime (mu 1) (arrival 1) candidate)
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
          (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) candidate) <=
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
          (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) := by
    simpa [gn21AggregateDynamicRewardFunctional,
      gn21MeasuredAggregateRewardPrimitives, Function.update] using hupdate
  have hlinear_raw :=
    gn21AggregateDynamicReward_candidate_right_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 candidate)
      (gn21ScaledStateTime (mu 1) (arrival 1) candidate)
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) candidate)
      hden_pos hden'_pos hquot
  have hlinear :
      gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate <=
        gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 1) := by
    simpa [gn21MeasuredRightLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) candidate hq_candidate hw_candidate
      htime_candidate
  have hscore_current :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) (rho 1) hq_current hw_current
      htime_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith

/--
At a source-open optimum, deleting the surge coordinate to the open empty
policy yields the fixed-marginal empty-policy comparison used by the finite
increasing-tail argument.
-/
theorem gn21MeasuredRightMarginalSetReward_empty_le_of_dynamicOpenOptimal_direct
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1)) :
    lemma5MarginalSetReward (mu 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (∅ : TripPolicy) <=
      lemma5MarginalSetReward (mu 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (rho 1) := by
  have hempty_open : dynamicFeasibleOpenPolicy (Function.update rho 1 ∅) := by
    intro i
    by_cases hi : i = 1
    · subst i
      exact ⟨by simp [Function.update], by simpa [Function.update] using isOpen_empty⟩
    · simpa [Function.update, hi] using hrho.1 i
  have hempty_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1 ∅) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho :=
    hrho.2 _ hempty_open
  exact gn21MeasuredRightMarginalSetReward_candidate_le_of_aggregate_update_le_direct
    mu arrival switch12 switch21 w harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hq1 hw1 htime1 hrho.1.to_measurable
    ∅ (by simp) MeasurableSet.empty hempty_reward

end GN21DriverSurgePricing
