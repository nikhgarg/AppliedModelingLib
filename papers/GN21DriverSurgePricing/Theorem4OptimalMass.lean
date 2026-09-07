import GN21DriverSurgePricing.DomainBridge

/-!
# Positive surge mass at a GN21 Theorem 4 optimum

The source permits the open empty policy, so positive accepted mass may not be
inserted as a hidden domain condition.  This module derives the one
positive-mass fact needed for the finite negative-affine surge cutoff directly
from source surge dominance and global open optimality.
-/

open AppliedModelingLib
open MeasureTheory

namespace GN21DriverSurgePricing

/--
At a source-open optimum, the surge component has positive accepted mass.

If its mass were zero, its state rate would be zero.  Source surge dominance
forces the other current state rate below it, so the Appendix-D aggregate
would be negative.  The all-empty open policy has aggregate reward zero,
contradicting optimality.
-/
theorem gn21PositiveSurgeMass_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
    (mu : Fin 2 -> Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicOpenOptimal
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho) :
    0 < singleStateTripMass (mu 1) (rho 1) := by
  have hrate_order :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
        gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) :=
    gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  by_contra hmass_not_pos
  have hmass_zero : singleStateTripMass (mu 1) (rho 1) = 0 := by
    apply le_antisymm
    · exact le_of_not_gt hmass_not_pos
    · exact singleStateTripMass_nonneg (mu 1) (rho 1)
  have hrate1_zero :
      gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) = 0 :=
    gn21MeasuredStateRewardRate_eq_zero_of_mass_zero_of_ne_top
      (arrival 1) hmass_zero (measure_ne_top (mu 1) (rho 1))
  have hrate0_neg :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) < 0 := by
    simpa [hrate1_zero] using hrate_order
  have hrho_meas : dynamicFeasibleMeasurablePolicy rho := hrho.1.to_measurable
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
      switch21 (rho 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      (hrho_meas 0).2 (hrho_meas 0).1
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21
      switch12 (rho 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      (hrho_meas 1).2 (hrho_meas 1).1
  have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (rho 0)
      (le_of_lt harrival0_pos) (hrho_meas 0).2 (hrho_meas 0).1
  have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (rho 1)
      (le_of_lt harrival1_pos) (hrho_meas 1).2 (hrho_meas 1).1
  have hW0 :
      gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0) =
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) *
          gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 0) (arrival 0)
      (gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0))
      (w 0) (rho 0) harrival0_pos (hrho_meas 0).2 (hrho_meas 0).1 rfl
  have hW1 :
      gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1) =
        gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) *
          gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 1) (arrival 1)
      (gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1))
      (w 1) (rho 1) harrival1_pos (hrho_meas 1).2 (hrho_meas 1).1 rfl
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hcurrent_neg :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho < 0 := by
    change
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
          (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) < 0
    rw [hW0, hW1, hrate1_zero]
    unfold gn21AggregateDynamicReward
    rw [div_lt_iff₀ hden_pos]
    have hrate_time_neg :
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) < 0 :=
      mul_neg_of_neg_of_pos hrate0_neg hT0_pos
    have hweighted_neg :
        gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            (gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) *
              gn21ScaledStateTime (mu 0) (arrival 0) (rho 0)) < 0 :=
      mul_neg_of_pos_of_neg hQ1_pos hrate_time_neg
    nlinarith
  let emptyPolicy : Fin 2 -> TripPolicy := fun _ => ∅
  have hempty_open : dynamicFeasibleOpenPolicy emptyPolicy := by
    intro i
    exact ⟨by
      intro tau htau
      exact False.elim htau, isOpen_empty⟩
  have hempty_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w emptyPolicy = 0 := by
    simp [emptyPolicy, gn21AggregateDynamicRewardFunctional,
      gn21MeasuredAggregateRewardPrimitives, gn21AggregateDynamicReward,
      gn21ExitWeightIntegral_empty, gn21ScaledStateTime_empty,
      gn21ScaledStateEarning_empty]
  have hoptimal_empty :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w emptyPolicy <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho :=
    hrho.2 emptyPolicy hempty_open
  rw [hempty_reward] at hoptimal_empty
  exact (not_lt_of_ge hoptimal_empty) hcurrent_neg

end GN21DriverSurgePricing
