import AppliedModelingLib.Foundations.Math.ConvexCombination
import GN21DriverSurgePricing.MainTheorems
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Domain Bridges for GN21 Measurable Theorem 3

The source policy domain consists of measurable unions of open intervals,
whereas several analytic bridges are naturally stated over all measurable
policies.  This file makes both that open-to-measurable bridge and the
positive-mass-to-full-domain bridge explicit.  In particular, an open-domain
optimizer lifts only after regular open approximation and reward continuity;
the proof never silently identifies the two policy domains.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal symmDiff

namespace GN21DriverSurgePricing

/-- Source-feasible dynamic policies: each accepted-trip set is open in the
ambient trip-length line and contained in the positive-trip domain. -/
def dynamicFeasibleOpenPolicy (σ : Fin 2 → TripPolicy) : Prop :=
  ∀ i : Fin 2, σ i ⊆ acceptAllPolicy ∧ IsOpen (σ i)

/-- Open-policy optimality used in GN21 Section 2.2 and Appendix D. -/
def dynamicOpenOptimal (R : DynamicReward) (σ : Fin 2 → TripPolicy) : Prop :=
  dynamicFeasibleOpenPolicy σ ∧
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy ρ → R ρ ≤ R σ

/--
The Appendix-D aggregate reward specialized to Theorem 3's structured CTMC
price family.  Unlike the state-rate/time-fraction quotient, this expression
retains the waiting-time term at an empty accepted-trip policy, which is needed
because the source policy domain permits open empty sets.
-/
noncomputable def gn21AggregateCTMCStructuredDynamicReward
    (μ : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) (m z : Fin 2 → ℝ) : DynamicReward :=
  gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)

/-- The source's definition of state 2 as a surge state: one open state-2
policy gives a strictly higher state reward rate than every feasible open
state-1 policy.  This is a model premise, not a conclusion package. -/
def gn21SourceSurgeStateDominance
    (μ : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (w : Fin 2 → PricingFunction) : Prop :=
  ∃ σ2 : TripPolicy,
    σ2 ⊆ acceptAllPolicy ∧ IsOpen σ2 ∧
      ∀ σ1 : TripPolicy,
        σ1 ⊆ acceptAllPolicy → IsOpen σ1 →
          gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) σ1 <
            gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2

/--
The converse direction of the Appendix-D quotient-to-linearization step for a
left-state policy replacement.  A nonnegative fixed-current linear score is
equivalent to weak improvement of the aggregate reward once the candidate
denominator is positive.
-/
theorem gn21AggregateDynamicReward_current_le_left_candidate_of_linearScore_nonneg
    (Qi Qj Ti Tj Wi Wj Qi' Ti' Wi' : ℝ)
    (hden'_pos : 0 < Qi' * Tj + Qj * Ti')
    (hscore :
      0 ≤ Qj *
          (Wi' - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Ti') +
        (Wj - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Tj) * Qi') :
    gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj ≤
      gn21AggregateDynamicReward Qi' Qj Ti' Tj Wi' Wj := by
  let r := gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj
  have hscore_eq :
      Qj * (Wi' - r * Ti') + (Wj - r * Tj) * Qi' =
        (Qi' * Wj + Qj * Wi') - r * (Qi' * Tj + Qj * Ti') := by
    ring
  change r ≤ (Qi' * Wj + Qj * Wi') / (Qi' * Tj + Qj * Ti')
  rw [le_div_iff₀ hden'_pos]
  rw [hscore_eq] at hscore
  linarith

/--
The state-swapped Appendix-D quotient-to-linearization bridge for a right-state
policy replacement.
-/
theorem gn21AggregateDynamicReward_current_le_right_candidate_of_linearScore_nonneg
    (Qi Qj Ti Tj Wi Wj Qj' Tj' Wj' : ℝ)
    (hden'_pos : 0 < Qi * Tj' + Qj' * Ti)
    (hscore :
      0 ≤ Qi *
          (Wj' - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Tj') +
        (Wi - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Ti) * Qj') :
    gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj ≤
      gn21AggregateDynamicReward Qi Qj' Ti Tj' Wi Wj' := by
  let r := gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj
  have hscore_eq :
      Qi * (Wj' - r * Tj') + (Wi - r * Ti) * Qj' =
        (Qi * Wj' + Qj' * Wi) - r * (Qi * Tj' + Qj' * Ti) := by
    ring
  change r ≤ (Qi * Wj' + Qj' * Wi) / (Qi * Tj' + Qj' * Ti)
  rw [le_div_iff₀ hden'_pos]
  rw [hscore_eq] at hscore
  linarith

/--
A left-state policy whose fixed-current marginal integral is at least the
current policy's integral weakly improves the Appendix-D aggregate reward.
All denominator and integrability facts are derived from the source primitive
domain, including the zero-accepted-mass endpoint.
-/
theorem gn21AggregateMultiplicativeDynamicReward_le_update_left_of_marginal_le
    (μ : Fin 2 → Measure TripLength)
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ)
    (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_measurable : MeasurableSet candidate)
    (hmarginal :
      lemma5MarginalSetReward (μ 0)
          (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))
          (ρ 0) ≤
        lemma5MarginalSetReward (μ 0)
          (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))
          candidate) :
    gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
        (Function.update ρ 0 candidate) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ 0).1
  have hρ0_measurable : MeasurableSet (ρ 0) := (hρ 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ 1).1
  have hρ1_measurable : MeasurableSet (ρ 1) := (hρ 1).2
  have htime_candidate :
      IntegrableOn (fun τ : TripLength => τ) candidate (μ 0) :=
    htime0.mono_set hcandidate_subset
  have htime_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 0) (μ 0) :=
    htime0.mono_set hρ0_subset
  have hq_candidate :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        candidate (μ 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21
      candidate (le_of_lt hswitch12_pos) hsum0 hcandidate_subset
      hcandidate_measurable htime_candidate
  have hq_current :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        (ρ 0) (μ 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21
      (ρ 0) (le_of_lt hswitch12_pos) hsum0 hρ0_subset hρ0_measurable
      htime_current
  have hw_candidate :
      IntegrableOn (multiplicativePricing (m 0)) candidate (μ 0) :=
    integrableOn_multiplicativePricing (μ 0) (m 0) candidate htime_candidate
  have hw_current :
      IntegrableOn (multiplicativePricing (m 0)) (ρ 0) (μ 0) :=
    integrableOn_multiplicativePricing (μ 0) (m 0) (ρ 0) htime_current
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12
      switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hρ0_measurable hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21
      switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hρ1_measurable hρ1_subset
  have hT0'_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) candidate :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) candidate
      (le_of_lt harrival0_pos) hcandidate_measurable hcandidate_subset
  have hQ0'_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 candidate :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12
      switch21 candidate (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hcandidate_measurable hcandidate_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hden'_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 candidate *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) candidate :=
    add_pos (mul_pos hQ0'_pos hT1_pos) (mul_pos hQ1_pos hT0'_pos)
  have hscore_candidate :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) candidate hq_candidate hw_candidate htime_candidate
  have hscore_current :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) (ρ 0) hq_current hw_current htime_current
  have hlinear :
      gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) (ρ 0) ≤
        gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) candidate := by
    rw [hscore_current, hscore_candidate]
    nlinarith
  have hcurrent_zero :
      gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) (ρ 0) = 0 := by
    unfold gn21MeasuredLeftLinearScoreAtCurrent
    exact gn21AggregateDynamicReward_current_left_linear_score_eq_zero
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0)
        (multiplicativePricing (m 0)) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1)
        (multiplicativePricing (m 1)) (ρ 1)) hden_pos
  have hscore_nonneg :
      0 ≤
        gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) candidate := by
    linarith
  have hquot :=
    gn21AggregateDynamicReward_current_le_left_candidate_of_linearScore_nonneg
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0)
        (multiplicativePricing (m 0)) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1)
        (multiplicativePricing (m 1)) (ρ 1))
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 candidate)
      (gn21ScaledStateTime (μ 0) (arrival 0) candidate)
      (gn21ScaledStateEarning (μ 0) (arrival 0)
        (multiplicativePricing (m 0)) candidate)
      hden'_pos (by
        simpa [gn21MeasuredLeftLinearScoreAtCurrent, mul_comm, mul_left_comm,
          mul_assoc] using hscore_nonneg)
  simpa [gn21AggregateMultiplicativeDynamicReward,
    gn21AggregateDynamicRewardFunctional, gn21MeasuredAggregateRewardPrimitives,
    Function.update] using hquot

/--
The state-swapped aggregate-reward replacement lemma for a right-state policy.
-/
theorem gn21AggregateMultiplicativeDynamicReward_le_update_right_of_marginal_le
    (μ : Fin 2 → Measure TripLength)
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    {ρ : Fin 2 → TripPolicy} (hρ : dynamicFeasibleMeasurablePolicy ρ)
    (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_measurable : MeasurableSet candidate)
    (hmarginal :
      lemma5MarginalSetReward (μ 1)
          (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))
          (ρ 1) ≤
        lemma5MarginalSetReward (μ 1)
          (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
            (ρ 0) (ρ 1))
          candidate) :
    gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m ρ ≤
      gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m
        (Function.update ρ 1 candidate) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ 0).1
  have hρ0_measurable : MeasurableSet (ρ 0) := (hρ 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ 1).1
  have hρ1_measurable : MeasurableSet (ρ 1) := (hρ 1).2
  have htime_candidate :
      IntegrableOn (fun τ : TripLength => τ) candidate (μ 1) :=
    htime1.mono_set hcandidate_subset
  have htime_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 1) (μ 1) :=
    htime1.mono_set hρ1_subset
  have hq_candidate :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        candidate (μ 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12
      candidate (le_of_lt hswitch21_pos) hsum1 hcandidate_subset
      hcandidate_measurable htime_candidate
  have hq_current :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        (ρ 1) (μ 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12
      (ρ 1) (le_of_lt hswitch21_pos) hsum1 hρ1_subset hρ1_measurable
      htime_current
  have hw_candidate :
      IntegrableOn (multiplicativePricing (m 1)) candidate (μ 1) :=
    integrableOn_multiplicativePricing (μ 1) (m 1) candidate htime_candidate
  have hw_current :
      IntegrableOn (multiplicativePricing (m 1)) (ρ 1) (μ 1) :=
    integrableOn_multiplicativePricing (μ 1) (m 1) (ρ 1) htime_current
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_measurable hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_measurable hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12
      switch21 (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hρ0_measurable hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21
      switch12 (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hρ1_measurable hρ1_subset
  have hT1'_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) candidate :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) candidate
      (le_of_lt harrival1_pos) hcandidate_measurable hcandidate_subset
  have hQ1'_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 candidate :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21
      switch12 candidate (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hcandidate_measurable hcandidate_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hden'_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) candidate +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 candidate *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1'_pos) (mul_pos hQ1'_pos hT0_pos)
  have hscore_candidate :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) candidate hq_candidate hw_candidate htime_candidate
  have hscore_current :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) (ρ 1) hq_current hw_current htime_current
  have hlinear :
      gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) (ρ 1) ≤
        gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) candidate := by
    rw [hscore_current, hscore_candidate]
    nlinarith
  have hcurrent_zero :
      gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) (ρ 1) = 0 := by
    unfold gn21MeasuredRightLinearScoreAtCurrent
    exact gn21AggregateDynamicReward_current_right_linear_score_eq_zero
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0)
        (multiplicativePricing (m 0)) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1)
        (multiplicativePricing (m 1)) (ρ 1)) hden_pos
  have hscore_nonneg :
      0 ≤
        gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (multiplicativePricing (m 0))
          (multiplicativePricing (m 1)) (ρ 0) (ρ 1) candidate := by
    linarith
  have hquot :=
    gn21AggregateDynamicReward_current_le_right_candidate_of_linearScore_nonneg
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0)
        (multiplicativePricing (m 0)) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1)
        (multiplicativePricing (m 1)) (ρ 1))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 candidate)
      (gn21ScaledStateTime (μ 1) (arrival 1) candidate)
      (gn21ScaledStateEarning (μ 1) (arrival 1)
        (multiplicativePricing (m 1)) candidate)
      hden'_pos (by
        simpa [gn21MeasuredRightLinearScoreAtCurrent, mul_comm, mul_left_comm,
          mul_assoc] using hscore_nonneg)
  simpa [gn21AggregateMultiplicativeDynamicReward,
    gn21AggregateDynamicRewardFunctional, gn21MeasuredAggregateRewardPrimitives,
    Function.update] using hquot

/-- Accept-all is a valid open policy in both source states. -/
theorem dynamicFeasibleOpenPolicy_acceptAllDynamicPolicy :
    dynamicFeasibleOpenPolicy acceptAllDynamicPolicy := by
  intro i
  constructor
  · exact fun _ hτ => hτ
  · simpa [acceptAllDynamicPolicy, acceptAllPolicy, positiveTripLengths,
      positiveRealAcceptAll] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

/-- Open source policies are feasible measurable policies. -/
theorem dynamicFeasibleOpenPolicy.to_measurable
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleOpenPolicy σ) :
    dynamicFeasibleMeasurablePolicy σ := by
  intro i
  exact ⟨(hσ i).1, (hσ i).2.measurableSet⟩

/-- Continuity of a dynamic reward when each state policy is perturbed in
measure.  This is the exact analytical condition needed to pass from the
source's open policy domain to all measurable policies. -/
def GN21DynamicSymmDiffContinuousAt
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (σ : Fin 2 → TripPolicy) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ τ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy τ →
        (∀ i : Fin 2, (μ i) (σ i ∆ τ i) < δ) →
          |R τ - R σ| < ε

/-- An integrable set integral is continuous under symmetric-difference
perturbations inside the positive-trip policy domain.  The proof uses the
absolute continuity of the Lebesgue integral, not a bounded-integrand
assumption. -/
theorem setIntegral_symmDiffContinuousAt_of_integrableOn
    (μ : Measure TripLength) (f : TripLength → ℝ)
    (hfin : IntegrableOn f acceptAllPolicy μ)
    {σ : TripPolicy}
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
        ∀ τ : TripPolicy,
          MeasurableSet τ → τ ⊆ acceptAllPolicy →
            μ (σ ∆ τ) < δ →
              |(∫ x in τ, f x ∂μ) - ∫ x in σ, f x ∂μ| < ε := by
  intro ε hε
  let g : TripLength → ℝ := acceptAllPolicy.indicator f
  have hg : Integrable g μ := by
    dsimp [g]
    exact hfin.integrable_indicator measurableSet_acceptAllPolicy
  have hhalf_pos : 0 < ε / 2 := by
    linarith
  have hfin_g : (∫⁻ x, ENNReal.ofReal |g x| ∂μ) ≠ ∞ := by
    exact ((hasFiniteIntegral_iff_norm g).mp hg.hasFiniteIntegral).ne
  have hhalf_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hhalf_pos).ne'
  rcases exists_pos_setLIntegral_lt_of_measure_lt hfin_g hhalf_ne with
    ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, ne_of_gt hδ_pos, ?_⟩
  intro τ hτ_measurable hτ_subset hclose
  have hsmall := hδ (σ ∆ τ) hclose
  have hsymm_integrable : IntegrableOn g (σ ∆ τ) μ := hg.integrableOn
  have hsymm_norm_eq :
      ∫ x in σ ∆ τ, |g x| ∂μ =
        (∫⁻ x in σ ∆ τ, ENNReal.ofReal |g x| ∂μ).toReal := by
    simpa only [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs] using
      (integral_norm_eq_lintegral_enorm hsymm_integrable.aestronglyMeasurable)
  have hsmall_real : ∫ x in σ ∆ τ, |g x| ∂μ < ε / 2 := by
    rw [hsymm_norm_eq]
    have hto :
        (∫⁻ x in σ ∆ τ, ENNReal.ofReal |g x| ∂μ).toReal <
          (ENNReal.ofReal (ε / 2)).toReal :=
      (ENNReal.toReal_lt_toReal
        (ne_top_of_lt (lt_of_lt_of_le hsmall le_top)) ENNReal.ofReal_ne_top).mpr hsmall
    simpa [ENNReal.toReal_ofReal hhalf_pos.le] using hto
  have hleft_subset : σ \ τ ⊆ σ ∆ τ := by
    rw [Set.symmDiff_def]
    exact Set.subset_union_left
  have hright_subset : τ \ σ ⊆ σ ∆ τ := by
    rw [Set.symmDiff_def]
    exact Set.subset_union_right
  have hleft_small : |∫ x in σ \ τ, g x ∂μ| < ε / 2 := by
    calc
      |∫ x in σ \ τ, g x ∂μ| ≤ ∫ x in σ \ τ, |g x| ∂μ := by
        simpa using
          (abs_integral_le_integral_abs (μ := μ.restrict (σ \ τ)) (f := g))
      _ ≤ ∫ x in σ ∆ τ, |g x| ∂μ := by
        exact setIntegral_mono_set hsymm_integrable.norm
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall hleft_subset)
      _ < ε / 2 := hsmall_real
  have hright_small : |∫ x in τ \ σ, g x ∂μ| < ε / 2 := by
    calc
      |∫ x in τ \ σ, g x ∂μ| ≤ ∫ x in τ \ σ, |g x| ∂μ := by
        simpa using
          (abs_integral_le_integral_abs (μ := μ.restrict (τ \ σ)) (f := g))
      _ ≤ ∫ x in σ ∆ τ, |g x| ∂μ := by
        exact setIntegral_mono_set hsymm_integrable.norm
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall hright_subset)
      _ < ε / 2 := hsmall_real
  have hdiff_g :
      (∫ x in τ, g x ∂μ) - ∫ x in σ, g x ∂μ =
        (∫ x in τ \ σ, g x ∂μ) - ∫ x in σ \ τ, g x ∂μ := by
    have hτ_decomp :=
      integral_inter_add_diff hσ_measurable (hg.integrableOn : IntegrableOn g τ μ)
    have hσ_decomp :=
      integral_inter_add_diff hτ_measurable (hg.integrableOn : IntegrableOn g σ μ)
    rw [← hτ_decomp, ← hσ_decomp]
    simp only [Set.inter_comm]
    ring
  have hσ_g : ∫ x in σ, f x ∂μ = ∫ x in σ, g x ∂μ := by
    apply setIntegral_congr_fun hσ_measurable
    intro x hx
    simpa [g] using (Set.indicator_of_mem (hσ_subset hx) f).symm
  have hτ_g : ∫ x in τ, f x ∂μ = ∫ x in τ, g x ∂μ := by
    apply setIntegral_congr_fun hτ_measurable
    intro x hx
    simpa [g] using (Set.indicator_of_mem (hτ_subset hx) f).symm
  rw [hτ_g, hσ_g, hdiff_g]
  calc
    |(∫ x in τ \ σ, g x ∂μ) - ∫ x in σ \ τ, g x ∂μ| ≤
        |∫ x in τ \ σ, g x ∂μ| + |∫ x in σ \ τ, g x ∂μ| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hright_small hleft_small
    _ = ε := by ring

/-- The Appendix-D aggregate multiplicative reward is continuous under
feasible policy symmetric-difference perturbations.  Together with regular
open approximation, this is the analytic input required to lift source-open
optimality to the measurable policy domain. -/
theorem gn21AggregateMultiplicativeDynamicReward_symmDiffContinuousAt
    (μ : Fin 2 → Measure TripLength)
    (arrival m : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ) :
    GN21DynamicSymmDiffContinuousAt μ
      (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) σ := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21
      acceptAllPolicy (le_of_lt hswitch12_pos) hsum0
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime0
  have hq1 :
      IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1) :=
    integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12
      acceptAllPolicy (le_of_lt hswitch21_pos) hsum1
      (fun _ hτ => hτ) measurableSet_acceptAllPolicy htime1
  let x : Fin 4 → ℝ := ![
    singleStateTripTime (μ 0) (σ 0),
    ∫ τ in σ 0, gn21SwitchProb switch12 switch21 τ ∂(μ 0),
    singleStateTripTime (μ 1) (σ 1),
    ∫ τ in σ 1, gn21SwitchProb switch21 switch12 τ ∂(μ 1)]
  let G : (Fin 4 → ℝ) → ℝ := fun v =>
    ((switch12 + arrival 0 * v 1) * (arrival 1 * m 1 * v 2) +
        (switch21 + arrival 1 * v 3) * (arrival 0 * m 0 * v 0)) /
      ((switch12 + arrival 0 * v 1) * (1 + arrival 1 * v 2) +
        (switch21 + arrival 1 * v 3) * (1 + arrival 0 * v 0))
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (σ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (σ 0)
      (le_of_lt harrival0_pos) (hσ 0).2 (hσ 0).1
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (σ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (σ 1)
      (le_of_lt harrival1_pos) (hσ 1).2 (hσ 1).1
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (σ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12 switch21
      (σ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0 (hσ 0).2 (hσ 0).1
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (σ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      (σ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1 (hσ 1).2 (hσ 1).1
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (σ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (σ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (σ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (σ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  have hGden :
      (switch12 + arrival 0 * x 1) * (1 + arrival 1 * x 2) +
        (switch21 + arrival 1 * x 3) * (1 + arrival 0 * x 0) ≠ 0 := by
    dsimp [x]
    simpa [gn21ExitWeightIntegral, gn21ScaledStateTime, singleStateTripTime] using hden_pos.ne'
  have hG_cont : ContinuousAt G x := by
    dsimp [G]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hGden
  intro ε hε
  rcases (Metric.continuousAt_iff.mp hG_cont) ε hε with ⟨η, hη_pos, hη⟩
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn (μ 0)
      (fun τ : TripLength => τ) htime0 (hσ 0).2 (hσ 0).1 η hη_pos with
    ⟨δt0, hδt0_ne, hδt0⟩
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn (μ 0)
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ) hq0
      (hσ 0).2 (hσ 0).1 η hη_pos with
    ⟨δq0, hδq0_ne, hδq0⟩
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn (μ 1)
      (fun τ : TripLength => τ) htime1 (hσ 1).2 (hσ 1).1 η hη_pos with
    ⟨δt1, hδt1_ne, hδt1⟩
  rcases setIntegral_symmDiffContinuousAt_of_integrableOn (μ 1)
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ) hq1
      (hσ 1).2 (hσ 1).1 η hη_pos with
    ⟨δq1, hδq1_ne, hδq1⟩
  let δ : ℝ≥0∞ := min δt0 (min δq0 (min δt1 δq1))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (pos_iff_ne_zero.mpr hδt0_ne)
      (lt_min (pos_iff_ne_zero.mpr hδq0_ne)
        (lt_min (pos_iff_ne_zero.mpr hδt1_ne) (pos_iff_ne_zero.mpr hδq1_ne)))
  refine ⟨δ, ne_of_gt hδ_pos, ?_⟩
  intro τ hτ hclose
  let y : Fin 4 → ℝ := ![
    singleStateTripTime (μ 0) (τ 0),
    ∫ u in τ 0, gn21SwitchProb switch12 switch21 u ∂(μ 0),
    singleStateTripTime (μ 1) (τ 1),
    ∫ u in τ 1, gn21SwitchProb switch21 switch12 u ∂(μ 1)]
  have htime0_close : |y 0 - x 0| < η := by
    dsimp [x, y, singleStateTripTime]
    apply hδt0 (τ 0) (hτ 0).2 (hτ 0).1
    exact lt_of_lt_of_le (hclose 0) (by simp [δ])
  have hq0_close : |y 1 - x 1| < η := by
    dsimp [x, y]
    apply hδq0 (τ 0) (hτ 0).2 (hτ 0).1
    exact lt_of_lt_of_le (hclose 0) (by simp [δ])
  have htime1_close : |y 2 - x 2| < η := by
    dsimp [x, y, singleStateTripTime]
    apply hδt1 (τ 1) (hτ 1).2 (hτ 1).1
    exact lt_of_lt_of_le (hclose 1) (by simp [δ])
  have hq1_close : |y 3 - x 3| < η := by
    dsimp [x, y]
    apply hδq1 (τ 1) (hτ 1).2 (hτ 1).1
    exact lt_of_lt_of_le (hclose 1) (by simp [δ])
  have hyx : dist y x < η := by
    rw [dist_pi_lt_iff hη_pos]
    intro i
    fin_cases i
    · simpa [Real.dist_eq] using htime0_close
    · simpa [Real.dist_eq] using hq0_close
    · simpa [Real.dist_eq] using htime1_close
    · simpa [Real.dist_eq] using hq1_close
  have hmap_close : dist (G y) (G x) < ε := hη hyx
  have hGx :
      G x = gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m σ := by
    dsimp [G, x]
    rw [gn21AggregateMultiplicativeDynamicReward_apply]
    unfold gn21MeasuredAggregateRewardPrimitives gn21AggregateDynamicReward
    rw [gn21ScaledStateEarning_multiplicativePricing,
      gn21ScaledStateEarning_multiplicativePricing]
    simp only [gn21ExitWeightIntegral, gn21ScaledStateTime, singleStateTripTime]
    ring
  have hGy :
      G y = gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m τ := by
    dsimp [G, y]
    rw [gn21AggregateMultiplicativeDynamicReward_apply]
    unfold gn21MeasuredAggregateRewardPrimitives gn21AggregateDynamicReward
    rw [gn21ScaledStateEarning_multiplicativePricing,
      gn21ScaledStateEarning_multiplicativePricing]
    simp only [gn21ExitWeightIntegral, gn21ScaledStateTime, singleStateTripTime]
    ring
  rw [hGy, hGx] at hmap_close
  simpa [Real.dist_eq] using hmap_close

/-- Replacing the right-state policy strictly improves the aggregate reward
when the old right reward rate is no larger than the left rate and the new
right reward rate is strictly larger.  This is the algebraic step used by the
source definition of the surge state. -/
theorem gn21AggregateDynamicReward_lt_of_right_rate_crosses_left
    (Qi Qj Qj' Ti Tj Tj' Wi Wj Wj' Ri Rj Rj' : ℝ)
    (hQi_pos : 0 < Qi) (hQj_pos : 0 < Qj) (hQj'_pos : 0 < Qj')
    (hTi_pos : 0 < Ti) (hTj_pos : 0 < Tj) (hTj'_pos : 0 < Tj')
    (hWi : Wi = Ri * Ti) (hWj : Wj = Rj * Tj)
    (hWj' : Wj' = Rj' * Tj')
    (hRj_le_Ri : Rj ≤ Ri) (hRi_lt_Rj' : Ri < Rj') :
    gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj <
      gn21AggregateDynamicReward Qi Qj' Ti Tj' Wi Wj' := by
  have hden : 0 < Qi * Tj + Qj * Ti :=
    gn21AggregateDenominator_pos_of_pos Qi Qj Ti Tj
      hQi_pos hQj_pos hTi_pos hTj_pos
  have hden' : 0 < Qi * Tj' + Qj' * Ti :=
    gn21AggregateDenominator_pos_of_pos Qi Qj' Ti Tj'
      hQi_pos hQj'_pos hTi_pos hTj'_pos
  have hold :
      gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj ≤ Ri := by
    rw [show gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj =
        (Qi * (Rj * Tj) + Qj * (Ri * Ti)) / (Qi * Tj + Qj * Ti) by
          simp [gn21AggregateDynamicReward, hWi, hWj]]
    rw [div_le_iff₀ hden]
    have hweight_nonneg : 0 ≤ Qi * Tj :=
      mul_nonneg (le_of_lt hQi_pos) (le_of_lt hTj_pos)
    nlinarith [mul_le_mul_of_nonneg_left hRj_le_Ri hweight_nonneg]
  have hnew :
      Ri < gn21AggregateDynamicReward Qi Qj' Ti Tj' Wi Wj' := by
    rw [show gn21AggregateDynamicReward Qi Qj' Ti Tj' Wi Wj' =
        (Qi * (Rj' * Tj') + Qj' * (Ri * Ti)) / (Qi * Tj' + Qj' * Ti) by
          simp [gn21AggregateDynamicReward, hWi, hWj']]
    rw [lt_div_iff₀ hden']
    have hweight_pos : 0 < Qi * Tj' := mul_pos hQi_pos hTj'_pos
    nlinarith [mul_pos hweight_pos (sub_pos.mpr hRi_lt_Rj')]
  exact hold.trans_lt hnew

/-- At a source-open optimum, the source surge-state premise forces the
current state-2 reward rate to exceed the current state-1 reward rate.  If it
did not, replacing state 2 by the source-dominating policy would strictly
raise the Appendix-D aggregate reward. -/
theorem gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge : gn21SourceSurgeStateDominance μ arrival w)
    {ρ : Fin 2 → TripPolicy}
    (hρ : dynamicOpenOptimal
      (gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w) ρ) :
    gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) <
      gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1) := by
  rcases hsurge with ⟨σ2, hσ2_subset, hσ2_open, hdominates⟩
  by_contra hnot
  have hRj_le_Ri :
      gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1) ≤
        gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) :=
    le_of_not_gt hnot
  have hRi_lt_Rj' :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) <
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2 :=
    hdominates (ρ 0) (hρ.1 0).1 (hρ.1 0).2
  let ρ' : Fin 2 → TripPolicy := Function.update ρ 1 σ2
  have hρ'_open : dynamicFeasibleOpenPolicy ρ' := by
    intro i
    fin_cases i
    · simpa [ρ'] using hρ.1 0
    · simpa [ρ'] using ⟨hσ2_subset, hσ2_open⟩
  have hρ'_le :
      gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w ρ' ≤
        gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w ρ :=
    hρ.2 ρ' hρ'_open
  have hρ_meas : dynamicFeasibleMeasurablePolicy ρ := hρ.1.to_measurable
  have hσ2_meas : MeasurableSet σ2 := hσ2_open.measurableSet
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hQi_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12 switch21
      (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      (hρ_meas 0).2 (hρ_meas 0).1
  have hQj_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      (hρ_meas 1).2 (hρ_meas 1).1
  have hQj'_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 σ2 :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      σ2 (le_of_lt harrival1_pos) hswitch21_pos hsum1 hσ2_meas hσ2_subset
  have hTi_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) (hρ_meas 0).2 (hρ_meas 0).1
  have hTj_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) (hρ_meas 1).2 (hρ_meas 1).1
  have hTj'_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) σ2 :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) σ2
      (le_of_lt harrival1_pos) hσ2_meas hσ2_subset
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0) =
        gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0) *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0)
      (gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0))
      (w 0) (ρ 0) harrival0_pos (hρ_meas 0).2 (hρ_meas 0).1 rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1) =
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1) *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1)
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1))
      (w 1) (ρ 1) harrival1_pos (hρ_meas 1).2 (hρ_meas 1).1 rfl
  have hWj' :
      gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) σ2 =
        gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2 *
          gn21ScaledStateTime (μ 1) (arrival 1) σ2 :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1)
      (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2)
      (w 1) σ2 harrival1_pos hσ2_meas hσ2_subset rfl
  have hlt :
      gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w ρ <
        gn21AggregateDynamicRewardFunctional μ arrival switch12 switch21 w ρ' := by
    change
      gn21MeasuredAggregateRewardPrimitives
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ 0) (ρ 1) <
        gn21MeasuredAggregateRewardPrimitives
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ' 0) (ρ' 1)
    simpa [gn21MeasuredAggregateRewardPrimitives, ρ'] using
      gn21AggregateDynamicReward_lt_of_right_rate_crosses_left
        (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
        (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
        (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 σ2)
        (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
        (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
        (gn21ScaledStateTime (μ 1) (arrival 1) σ2)
        (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
        (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
        (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) σ2)
        (gn21MeasuredStateRewardRate (μ 0) (arrival 0) (w 0) (ρ 0))
        (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) (ρ 1))
        (gn21MeasuredStateRewardRate (μ 1) (arrival 1) (w 1) σ2)
        hQi_pos hQj_pos hQj'_pos hTi_pos hTj_pos hTj'_pos hWi hWj hWj'
        hRj_le_Ri hRi_lt_Rj'
  exact (not_lt_of_ge hρ'_le) hlt

/-- A positive-mass accepted policy cannot have a strictly negative marginal
response everywhere when its marginal reward is at least that of the empty
policy.  This is the exact comparison used by the cutoff arguments below. -/
lemma lemma5MarginalSetReward_not_emptyComparison_of_response_negative_on_policy
    (μ : Measure TripLength) (response : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hint : IntegrableOn response acceptAllPolicy μ)
    (hneg : ∀ τ : TripLength, τ ∈ σ → response τ < 0)
    (hempty_comparison :
      lemma5MarginalSetReward μ response ∅ ≤
        lemma5MarginalSetReward μ response σ) : False := by
  have hmeasure_pos : 0 < μ σ :=
    measure_pos_of_singleStateTripMass_pos μ σ hmass
  have hneg_integrable : IntegrableOn (fun τ => -response τ) σ μ :=
    hint.neg.mono_set hσ_subset
  have hnonneg_ae : 0 ≤ᵐ[μ.restrict σ] fun τ => -response τ :=
    (ae_restrict_iff' hσ_meas).2
      (Filter.Eventually.of_forall fun τ hτ =>
        le_of_lt (neg_pos.mpr (hneg τ hτ)))
  have hsupport : Function.support response ∩ σ = σ := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact ⟨ne_of_lt (hneg τ hτ), hτ⟩
  have hneg_integral_pos : 0 < ∫ τ in σ, -response τ ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg_ae hneg_integrable).2
      (by simpa [hsupport] using hmeasure_pos)
  have hneg_eq :
      (∫ τ in σ, -response τ ∂μ) = -(∫ τ in σ, response τ ∂μ) := by
    simpa using (integral_neg (μ := μ.restrict σ) (f := response))
  have hresponse_integral_neg : ∫ τ in σ, response τ ∂μ < 0 := by
    rw [hneg_eq] at hneg_integral_pos
    linarith
  have hresponse_integral_nonneg : 0 ≤ ∫ τ in σ, response τ ∂μ := by
    simpa [lemma5MarginalSetReward] using hempty_comparison
  linarith

/-- A positive-mass marginal-set optimum cannot integrate a response which is
strictly negative over its accepted policy: its full optimality hypothesis
supplies the empty-policy comparison required above. -/
lemma lemma5MarginalSetReward_not_optimal_of_response_negative_on_policy
    (μ : Measure TripLength) (response : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hint : IntegrableOn response acceptAllPolicy μ)
    (hneg : ∀ τ : TripLength, τ ∈ σ → response τ < 0)
    (hoptimal :
      ∀ τ : TripPolicy, τ ⊆ acceptAllPolicy → MeasurableSet τ →
        lemma5MarginalSetReward μ response τ ≤
          lemma5MarginalSetReward μ response σ) : False := by
  exact lemma5MarginalSetReward_not_emptyComparison_of_response_negative_on_policy
    μ response σ hσ_meas hσ_subset hmass hint hneg
    (hoptimal ∅ (by simp) MeasurableSet.empty)

/-- A continuous strictly decreasing Lemma-6 response at a positive-mass
marginal optimum is either positive on all positive trip lengths or has a
positive zero.  The excluded third case would be negative on the optimum's
accepted set and is ruled out by the empty-policy comparison. -/
theorem lemma5Positive_or_zero_of_strictAntiOn_marginal_optimal
    (μ : Measure TripLength) (response : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hint : IntegrableOn response acceptAllPolicy μ)
    (hoptimal :
      ∀ τ : TripPolicy, τ ⊆ acceptAllPolicy → MeasurableSet τ →
        lemma5MarginalSetReward μ response τ ≤
          lemma5MarginalSetReward μ response σ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      ∃ t : ℝ, 0 < t ∧ response t = 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : ∃ t : ℝ, 0 < t ∧ response t = 0
    · exact hzero
    · exfalso
      have hu_neg : response u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      have hneg_all : ∀ τ : TripLength, 0 < τ → response τ < 0 := by
        intro τ hτ_pos
        by_contra hτ_notneg
        have hτ_nonneg : 0 ≤ response τ := le_of_not_gt hτ_notneg
        rcases lt_or_eq_of_le hτ_nonneg with hresponseτ_pos | hτ_zero
        · have hτ_lt_u : τ < u := by
            by_contra hnot_lt
            rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
            · have hanti_lt : response τ < response u :=
                hanti hu_pos hτ_pos hlt
              linarith
            · subst τ
              linarith
          have hcont_interval : ContinuousOn response (Set.Icc τ u) :=
            hcont.mono (fun x hx => hτ_pos.trans_le hx.1)
          have hzero_between : (0 : ℝ) ∈ Set.Icc (response u) (response τ) :=
            ⟨le_of_lt hu_neg, le_of_lt hresponseτ_pos⟩
          rcases intermediate_value_Icc' (le_of_lt hτ_lt_u) hcont_interval hzero_between with
            ⟨t, ht, ht_zero⟩
          exact hzero ⟨t, hτ_pos.trans_le ht.1, ht_zero⟩
        · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)
      exact
        lemma5MarginalSetReward_not_optimal_of_response_negative_on_policy
          μ response σ hσ_meas hσ_subset hmass hint
          (fun τ hτ => hneg_all τ (hσ_subset hτ)) hoptimal

/-- Strictly increasing counterpart of
`lemma5Positive_or_zero_of_strictAntiOn_marginal_optimal`. -/
theorem lemma5Positive_or_zero_of_strictMonoOn_marginal_optimal
    (μ : Measure TripLength) (response : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hint : IntegrableOn response acceptAllPolicy μ)
    (hoptimal :
      ∀ τ : TripPolicy, τ ⊆ acceptAllPolicy → MeasurableSet τ →
        lemma5MarginalSetReward μ response τ ≤
          lemma5MarginalSetReward μ response σ)
    (hcont : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      ∃ t : ℝ, 0 < t ∧ response t = 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < response τ
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : ∃ t : ℝ, 0 < t ∧ response t = 0
    · exact hzero
    · exfalso
      have hu_neg : response u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      have hneg_all : ∀ τ : TripLength, 0 < τ → response τ < 0 := by
        intro τ hτ_pos
        by_contra hτ_notneg
        have hτ_nonneg : 0 ≤ response τ := le_of_not_gt hτ_notneg
        rcases lt_or_eq_of_le hτ_nonneg with hresponseτ_pos | hτ_zero
        · have hu_lt_τ : u < τ := by
            by_contra hnot_lt
            rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
            · have hmono_lt : response τ < response u :=
                hmono hτ_pos hu_pos hlt
              linarith
            · subst τ
              linarith
          have hcont_interval : ContinuousOn response (Set.Icc u τ) :=
            hcont.mono (fun x hx => hu_pos.trans_le hx.1)
          have hzero_between : (0 : ℝ) ∈ Set.Icc (response u) (response τ) :=
            ⟨le_of_lt hu_neg, le_of_lt hresponseτ_pos⟩
          rcases intermediate_value_Icc (le_of_lt hu_lt_τ) hcont_interval hzero_between with
            ⟨t, ht, ht_zero⟩
          exact hzero ⟨t, hu_pos.trans_le ht.1, ht_zero⟩
        · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)
      exact
        lemma5MarginalSetReward_not_optimal_of_response_negative_on_policy
          μ response σ hσ_meas hσ_subset hmass hint
          (fun τ hτ => hneg_all τ (hσ_subset hτ)) hoptimal

/-- Version of the decreasing-response cutoff dichotomy for a normalized
Lemma-6 response whose sign is transferred to the actual marginal objective
by a positive, policy-dependent scale factor.  Only comparison with the empty
policy is needed to exclude the all-negative branch. -/
theorem lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_emptyComparison
    (μ : Measure TripLength) (base marginal : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hmarg_integrable : IntegrableOn marginal acceptAllPolicy μ)
    (hempty_comparison :
      lemma5MarginalSetReward μ marginal ∅ ≤
        lemma5MarginalSetReward μ marginal σ)
    (hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hanti : StrictAntiOn base (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < base τ) ∨
      ∃ t : ℝ, 0 < t ∧ base t = 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < base τ
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : ∃ t : ℝ, 0 < t ∧ base t = 0
    · exact hzero
    · exfalso
      have hu_neg : base u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      have hneg_all : ∀ τ : TripLength, 0 < τ → base τ < 0 := by
        intro τ hτ_pos
        by_contra hτ_notneg
        have hτ_nonneg : 0 ≤ base τ := le_of_not_gt hτ_notneg
        rcases lt_or_eq_of_le hτ_nonneg with hbaseτ_pos | hτ_zero
        · have hτ_lt_u : τ < u := by
            by_contra hnot_lt
            rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
            · have hanti_lt : base τ < base u := hanti hu_pos hτ_pos hlt
              linarith
            · subst τ
              linarith
          have hcont_interval : ContinuousOn base (Set.Icc τ u) :=
            hcont.mono (fun x hx => hτ_pos.trans_le hx.1)
          have hzero_between : (0 : ℝ) ∈ Set.Icc (base u) (base τ) :=
            ⟨le_of_lt hu_neg, le_of_lt hbaseτ_pos⟩
          rcases intermediate_value_Icc' (le_of_lt hτ_lt_u) hcont_interval hzero_between with
            ⟨t, ht, ht_zero⟩
          exact hzero ⟨t, hτ_pos.trans_le ht.1, ht_zero⟩
        · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)
      exact
        lemma5MarginalSetReward_not_emptyComparison_of_response_negative_on_policy
          μ marginal σ hσ_meas hσ_subset hmass hmarg_integrable
          (fun τ hτ =>
            hnegative_transfer τ (hσ_subset hτ) (hneg_all τ (hσ_subset hτ)))
          hempty_comparison

/-- Full fixed-marginal optimality supplies the empty-policy comparison used
by `lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_emptyComparison`. -/
theorem lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_optimal
    (μ : Measure TripLength) (base marginal : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hmarg_integrable : IntegrableOn marginal acceptAllPolicy μ)
    (hoptimal :
      ∀ τ : TripPolicy, τ ⊆ acceptAllPolicy → MeasurableSet τ →
        lemma5MarginalSetReward μ marginal τ ≤
          lemma5MarginalSetReward μ marginal σ)
    (hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hanti : StrictAntiOn base (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < base τ) ∨
      ∃ t : ℝ, 0 < t ∧ base t = 0 := by
  exact lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_emptyComparison
    μ base marginal σ hσ_meas hσ_subset hmass hmarg_integrable
    (hoptimal ∅ (by simp) MeasurableSet.empty) hnegative_transfer hcont hanti

/-- Increasing-response counterpart of
`lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_emptyComparison`.
Only comparison with the empty policy is needed to exclude the all-negative
branch. -/
theorem lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_emptyComparison
    (μ : Measure TripLength) (base marginal : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hmarg_integrable : IntegrableOn marginal acceptAllPolicy μ)
    (hempty_comparison :
      lemma5MarginalSetReward μ marginal ∅ ≤
        lemma5MarginalSetReward μ marginal σ)
    (hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hmono : StrictMonoOn base (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < base τ) ∨
      ∃ t : ℝ, 0 < t ∧ base t = 0 := by
  by_cases hpositive : ∀ τ : TripLength, 0 < τ → 0 < base τ
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : ∃ t : ℝ, 0 < t ∧ base t = 0
    · exact hzero
    · exfalso
      have hu_neg : base u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      have hneg_all : ∀ τ : TripLength, 0 < τ → base τ < 0 := by
        intro τ hτ_pos
        by_contra hτ_notneg
        have hτ_nonneg : 0 ≤ base τ := le_of_not_gt hτ_notneg
        rcases lt_or_eq_of_le hτ_nonneg with hbaseτ_pos | hτ_zero
        · have hu_lt_τ : u < τ := by
            by_contra hnot_lt
            rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
            · have hmono_lt : base τ < base u := hmono hτ_pos hu_pos hlt
              linarith
            · subst τ
              linarith
          have hcont_interval : ContinuousOn base (Set.Icc u τ) :=
            hcont.mono (fun x hx => hu_pos.trans_le hx.1)
          have hzero_between : (0 : ℝ) ∈ Set.Icc (base u) (base τ) :=
            ⟨le_of_lt hu_neg, le_of_lt hbaseτ_pos⟩
          rcases intermediate_value_Icc (le_of_lt hu_lt_τ) hcont_interval hzero_between with
            ⟨t, ht, ht_zero⟩
          exact hzero ⟨t, hu_pos.trans_le ht.1, ht_zero⟩
        · exact False.elim (hzero ⟨τ, hτ_pos, hτ_zero.symm⟩)
      exact
        lemma5MarginalSetReward_not_emptyComparison_of_response_negative_on_policy
          μ marginal σ hσ_meas hσ_subset hmass hmarg_integrable
          (fun τ hτ =>
            hnegative_transfer τ (hσ_subset hτ) (hneg_all τ (hσ_subset hτ)))
          hempty_comparison

/-- Full fixed-marginal optimality supplies the empty-policy comparison used
by `lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_emptyComparison`. -/
theorem lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_optimal
    (μ : Measure TripLength) (base marginal : TripLength → ℝ) (σ : TripPolicy)
    (hσ_meas : MeasurableSet σ) (hσ_subset : σ ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass μ σ)
    (hmarg_integrable : IntegrableOn marginal acceptAllPolicy μ)
    (hoptimal :
      ∀ τ : TripPolicy, τ ⊆ acceptAllPolicy → MeasurableSet τ →
        lemma5MarginalSetReward μ marginal τ ≤
          lemma5MarginalSetReward μ marginal σ)
    (hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0)
    (hcont : ContinuousOn base (Set.Ioi 0))
    (hmono : StrictMonoOn base (Set.Ioi 0)) :
    (∀ τ : TripLength, 0 < τ → 0 < base τ) ∨
      ∃ t : ℝ, 0 < t ∧ base t = 0 := by
  exact lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_emptyComparison
    μ base marginal σ hσ_meas hσ_subset hmass hmarg_integrable
    (hoptimal ∅ (by simp) MeasurableSet.empty) hnegative_transfer hcont hmono

/-- The normalized left-state Lemma-6 response for multiplicative pricing is
continuous over the source's positive-trip domain. -/
theorem continuousOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI m Ri Rj : ℝ)
    (σI σJ : TripPolicy) :
    ContinuousOn
      (gn21MeasuredLeftLemma6ResponseAtCurrent μI μJ arrivalI arrivalJ
        switchIJ switchJI (multiplicativePricing m) σI σJ Ri Rj)
      (Set.Ioi 0) := by
  simpa [gn21MeasuredLeftLemma6ResponseAtCurrent] using
    (show ContinuousOn
      (fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb switchIJ switchJI u) u
          (multiplicativePricing m u)
          (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
          (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
          (gn21ScaledStateTime μI arrivalI σI)
          (gn21ScaledStateTime μJ arrivalJ σJ) Ri Rj)
      (Set.Ioi 0) from by
        intro u hu
        have hu_ne : u ≠ 0 := ne_of_gt hu
        unfold gn21Lemma6Response multiplicativePricing
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.sub
        · apply ContinuousAt.add
          · exact
              ((continuous_gn21SwitchProb switchIJ switchJI).continuousAt.div
                continuousAt_id hu_ne).mul continuousAt_const
          · exact
              (((continuousAt_const.mul continuousAt_id).div continuousAt_id hu_ne).mul
                continuousAt_const)
        · fun_prop)

/-- Right-state counterpart of
`continuousOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative`. -/
theorem continuousOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI m Ri Rj : ℝ)
    (σI σJ : TripPolicy) :
    ContinuousOn
      (gn21MeasuredRightLemma6ResponseAtCurrent μI μJ arrivalI arrivalJ
        switchIJ switchJI (multiplicativePricing m) σI σJ Ri Rj)
      (Set.Ioi 0) := by
  simpa [gn21MeasuredRightLemma6ResponseAtCurrent] using
    (show ContinuousOn
      (fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb switchJI switchIJ u) u
          (multiplicativePricing m u)
          (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
          (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
          (gn21ScaledStateTime μJ arrivalJ σJ)
          (gn21ScaledStateTime μI arrivalI σI) Rj Ri)
      (Set.Ioi 0) from by
        intro u hu
        have hu_ne : u ≠ 0 := ne_of_gt hu
        unfold gn21Lemma6Response multiplicativePricing
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.sub
        · apply ContinuousAt.add
          · exact
              ((continuous_gn21SwitchProb switchJI switchIJ).continuousAt.div
                continuousAt_id hu_ne).mul continuousAt_const
          · exact
              (((continuousAt_const.mul continuousAt_id).div continuousAt_id hu_ne).mul
                continuousAt_const)
        · fun_prop)

/-- At a state-rate-ordered policy, the normalized multiplicative non-surge
Lemma-6 response is strictly decreasing. -/
theorem strictAntiOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI m Ri Rj : ℝ)
    (σI σJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI) :
    StrictAntiOn
      (gn21MeasuredLeftLemma6ResponseAtCurrent μI μJ arrivalI arrivalJ
        switchIJ switchJI (multiplicativePricing m) σI σJ Ri Rj)
      (Set.Ioi 0) := by
  simpa [gn21MeasuredLeftLemma6ResponseAtCurrent, multiplicativePricing] using
    (strictAntiOn_gn21Lemma6Response_structured_ctmc_of_coeff_pos
      m 0
      (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
      (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
      (gn21ScaledStateTime μI arrivalI σI)
      (gn21ScaledStateTime μJ arrivalJ σJ)
      Ri Rj switchIJ switchJI
      (by linarith) hswitch_pos hsum)

/-- At a state-rate-ordered policy, the normalized multiplicative surge
Lemma-6 response is strictly increasing. -/
theorem strictMonoOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI m Ri Rj : ℝ)
    (σI σJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (hswitch_pos : 0 < switchJI)
    (hsum : 0 < switchJI + switchIJ) :
    StrictMonoOn
      (gn21MeasuredRightLemma6ResponseAtCurrent μI μJ arrivalI arrivalJ
        switchIJ switchJI (multiplicativePricing m) σI σJ Ri Rj)
      (Set.Ioi 0) := by
  simpa [gn21MeasuredRightLemma6ResponseAtCurrent, multiplicativePricing] using
    (strictMonoOn_gn21Lemma6Response_structured_ctmc_of_coeff_neg
      m 0
      (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
      (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
      (gn21ScaledStateTime μJ arrivalJ σJ)
      (gn21ScaledStateTime μI arrivalI σI)
      Rj Ri switchJI switchIJ
      (by linarith) hswitch_pos hsum)

/-- Every feasible measurable two-state policy has an open feasible
approximation in each state.  Intersecting the regular open superset with the
positive-trip domain preserves feasibility. -/
theorem exists_dynamicFeasibleOpenPolicy_symmDiff_lt
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ τ : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy τ ∧
        ∀ i : Fin 2, (μ i) (σ i ∆ τ i) < ε := by
  have hopen_acceptAll : IsOpen acceptAllPolicy := by
    simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
      (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  have happrox :
      ∀ i : Fin 2, ∃ U : TripPolicy,
        σ i ⊆ U ∧ IsOpen U ∧ (μ i) U < ∞ ∧ (μ i) (U \ σ i) < ε := by
    intro i
    fin_cases i
    · exact
        (hσ 0).2.exists_isOpen_diff_lt (measure_ne_top (μ 0) (σ 0)) hε
    · exact
        (hσ 1).2.exists_isOpen_diff_lt (measure_ne_top (μ 1) (σ 1)) hε
  choose U hσU hUopen _hUfinite hdiff using happrox
  let τ : Fin 2 → TripPolicy := fun i => U i ∩ acceptAllPolicy
  refine ⟨τ, ?_, ?_⟩
  · intro i
    exact ⟨by intro x hx; exact hx.2, (hUopen i).inter hopen_acceptAll⟩
  · intro i
    have hσ_subset_τ : σ i ⊆ τ i := by
      intro x hx
      exact ⟨hσU i hx, (hσ i).1 hx⟩
    have hsymm : σ i ∆ τ i = τ i \ σ i := by
      rw [Set.symmDiff_def, Set.diff_eq_empty.2 hσ_subset_τ, Set.empty_union]
    rw [hsymm]
    apply (measure_mono ?_).trans_lt (hdiff i)
    intro x hx
    have hxτ : x ∈ U i ∩ acceptAllPolicy := by
      simpa [τ] using hx.1
    exact ⟨hxτ.1, hx.2⟩

/-- Under regular open approximation and dynamic reward continuity at every
feasible measurable deviation, the source's open-domain optimizer is also a
measurable-domain optimizer. -/
theorem dynamicMeasurableOptimal_of_dynamicOpenOptimal
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicOpenOptimal R σ)
    (hcont :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy ρ →
          GN21DynamicSymmDiffContinuousAt μ R ρ) :
    dynamicMeasurableOptimal R σ := by
  constructor
  · exact hσ.1.to_measurable
  · intro ρ hρ
    by_contra hnot
    have hlt : R σ < R ρ := lt_of_not_ge hnot
    let ε : ℝ := (R ρ - R σ) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    rcases hcont ρ hρ ε hε with ⟨δ, hδ_ne, hδ⟩
    rcases exists_dynamicFeasibleOpenPolicy_symmDiff_lt μ hρ hδ_ne with
      ⟨τ, hτ, hτ_close⟩
    have hreward_close : |R τ - R ρ| < ε := hδ τ hτ.to_measurable hτ_close
    have hσ_lt_τ : R σ < R τ := by
      rw [abs_lt] at hreward_close
      dsimp [ε] at hreward_close
      linarith
    have hτ_le : R τ ≤ R σ := hσ.2 τ hτ
    linarith

/-- The source surge-state premise and source-open optimality derive the
non-surge Lemma 6 branch needed in Theorem 2.  The normalized response carries
monotonicity; its negative sign is transferred to the actual marginal response
through the checked positive pointwise scale. -/
theorem gn21MultiplicativeNonsurgeResponseBranch_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ) (m : Fin 2 → ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hsurge : gn21SourceSurgeStateDominance μ arrival
      (fun i => multiplicativePricing (m i)))
    {ρ : Fin 2 → TripPolicy}
    (hρ : dynamicOpenOptimal
      (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) ρ)
    (hmass : 0 < singleStateTripMass (μ 0) (ρ 0)) :
    let response :=
      gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (multiplicativePricing (m 0)) (ρ 0) (ρ 1)
        (gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0))
        (gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1))
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      ∃ t : ℝ, 0 < t ∧ StrictAntiOn response (Set.Ioi 0) ∧ response t = 0 := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have htime0_all :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (μ 0) := by
    intro σ hσ _
    exact htime0.mono_set hσ
  have hq0 :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ) σ (μ 0) := by
    intro σ hσ hmeas
    exact integrableOn_gn21SwitchProb_of_time_integrable (μ 0) switch12 switch21 σ
      (le_of_lt hswitch12_pos) hsum0 hσ hmeas (htime0_all σ hσ hmeas)
  have hw0 :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 0)) σ (μ 0) := by
    intro σ hσ hmeas
    exact integrableOn_multiplicativePricing (μ 0) (m 0) σ
      (htime0_all σ hσ hmeas)
  have hρ_meas :
      dynamicMeasurableOptimal
        (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) ρ :=
    dynamicMeasurableOptimal_of_dynamicOpenOptimal μ
      (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) hρ
      (fun σ hσ =>
        gn21AggregateMultiplicativeDynamicReward_symmDiffContinuousAt μ arrival m
          switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos
          htime0 htime1 hσ)
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ_meas.1 0).1
  have hρ0_meas : MeasurableSet (ρ 0) := (hρ_meas.1 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ_meas.1 1).1
  have hρ1_meas : MeasurableSet (ρ 1) := (hρ_meas.1 1).2
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_meas hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_meas hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12 switch21
      (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0 hρ0_meas hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1 hρ1_meas hρ1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (μ 0) (arrival 0)
    (multiplicativePricing (m 0)) (ρ 0)
  let Rj := gn21MeasuredStateRewardRate (μ 1) (arrival 1)
    (multiplicativePricing (m 1)) (ρ 1)
  let base :=
    gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (ρ 0) (ρ 1) Ri Rj
  let marginal :=
    gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0) (multiplicativePricing (m 0)) (ρ 0) =
        Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0) Ri (multiplicativePricing (m 0)) (ρ 0)
      harrival0_pos hρ0_meas hρ0_subset rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1) (multiplicativePricing (m 1)) (ρ 1) =
        Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1) Rj (multiplicativePricing (m 1)) (ρ 1)
      harrival1_pos hρ1_meas hρ1_subset rfl
  have hbranch_optimal :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        lemma5MarginalSetReward (μ 0) marginal σ ≤
          lemma5MarginalSetReward (μ 0) marginal (ρ 0) := by
    intro σ hσ hmeas
    dsimp [marginal]
    exact lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_zero
      μ arrival switch12 switch21 (fun i => multiplicativePricing (m i)) hρ_meas
      harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hq0 hw0 htime0_all
      σ hσ hmeas
  have hmarginal_integrable : IntegrableOn marginal acceptAllPolicy (μ 0) := by
    dsimp [marginal]
    exact integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) acceptAllPolicy
      (hq0 acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      (hw0 acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      (htime0_all acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
  have hRi_lt_Rj : Ri < Rj := by
    dsimp [Ri, Rj]
    exact gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      μ arrival switch12 switch21 (fun i => multiplicativePricing (m i))
      harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hsurge hρ
  have hbase_cont : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    exact continuousOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 0) Ri Rj
      (ρ 0) (ρ 1)
  have hbase_anti : StrictAntiOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictAntiOn_gn21MeasuredLeftLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 0) Ri Rj
      (ρ 0) (ρ 1) hRi_lt_Rj hswitch12_pos hsum0
  have hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0 := by
    intro τ hτ hbase_neg
    have hscale_pos :
        0 < gn21MeasuredLeftLemma6ScaleAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) τ :=
      gn21MeasuredLeftLemma6ScaleAtCurrent_pos (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1)
        hQ1_pos hT0_pos hT1_pos hden_pos hτ
    have hscale_eq :
        marginal τ =
          gn21MeasuredLeftLemma6ScaleAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) τ * base τ := by
      dsimp [marginal, base]
      exact gn21MeasuredLeftMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
        (ρ 0) (ρ 1) Ri Rj τ (ne_of_gt hden_pos) (ne_of_gt hτ)
        (ne_of_gt hT0_pos) (ne_of_gt hT1_pos) hWi hWj
    rw [hscale_eq]
    exact mul_neg_of_pos_of_neg hscale_pos hbase_neg
  rcases lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_optimal
      (μ 0) base marginal (ρ 0) hρ0_meas hρ0_subset hmass hmarginal_integrable
      hbranch_optimal hnegative_transfer hbase_cont hbase_anti with hpositive | ⟨t, ht, hzero⟩
  · left
    simpa [base, Ri, Rj] using hpositive
  · right
    exact ⟨t, ht, by simpa [base, Ri, Rj] using hbase_anti,
      by simpa [base, Ri, Rj] using hzero⟩

/-- The source surge-state premise and source-open optimality derive the surge
Lemma 6 branch needed in Theorem 2.  As on the non-surge side, the proof keeps
the normalized response's monotonicity separate from the scaled marginal
response and transfers only its sign. -/
theorem gn21MultiplicativeSurgeResponseBranch_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ) (m : Fin 2 → ℝ)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime1 : IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hsurge : gn21SourceSurgeStateDominance μ arrival
      (fun i => multiplicativePricing (m i)))
    {ρ : Fin 2 → TripPolicy}
    (hρ : dynamicOpenOptimal
      (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) ρ)
    (hmass : 0 < singleStateTripMass (μ 1) (ρ 1)) :
    let response :=
      gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
        (gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (multiplicativePricing (m 0)) (ρ 0))
        (gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (multiplicativePricing (m 1)) (ρ 1))
    (∀ τ : TripLength, 0 < τ → 0 < response τ) ∨
      ∃ t : ℝ, 0 < t ∧ StrictMonoOn response (Set.Ioi 0) ∧ response t = 0 := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have htime1_all :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (μ 1) := by
    intro σ hσ _
    exact htime1.mono_set hσ
  have hq1 :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ) σ (μ 1) := by
    intro σ hσ hmeas
    exact integrableOn_gn21SwitchProb_of_time_integrable (μ 1) switch21 switch12 σ
      (le_of_lt hswitch21_pos) hsum1 hσ hmeas (htime1_all σ hσ hmeas)
  have hw1 :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        IntegrableOn (multiplicativePricing (m 1)) σ (μ 1) := by
    intro σ hσ hmeas
    exact integrableOn_multiplicativePricing (μ 1) (m 1) σ
      (htime1_all σ hσ hmeas)
  have hρ_meas :
      dynamicMeasurableOptimal
        (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) ρ :=
    dynamicMeasurableOptimal_of_dynamicOpenOptimal μ
      (gn21AggregateMultiplicativeDynamicReward μ arrival switch12 switch21 m) hρ
      (fun σ hσ =>
        gn21AggregateMultiplicativeDynamicReward_symmDiffContinuousAt μ arrival m
          switch12 switch21 harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos
          htime0 htime1 hσ)
  have hρ0_subset : ρ 0 ⊆ acceptAllPolicy := (hρ_meas.1 0).1
  have hρ0_meas : MeasurableSet (ρ 0) := (hρ_meas.1 0).2
  have hρ1_subset : ρ 1 ⊆ acceptAllPolicy := (hρ_meas.1 1).1
  have hρ1_meas : MeasurableSet (ρ 1) := (hρ_meas.1 1).2
  have hT0_pos : 0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
      (le_of_lt harrival0_pos) hρ0_meas hρ0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
      (le_of_lt harrival1_pos) hρ1_meas hρ1_subset
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0) switch12 switch21
      (ρ 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0 hρ0_meas hρ0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1) switch21 switch12
      (ρ 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1 hρ1_meas hρ1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (μ 0) (arrival 0)
    (multiplicativePricing (m 0)) (ρ 0)
  let Rj := gn21MeasuredStateRewardRate (μ 1) (arrival 1)
    (multiplicativePricing (m 1)) (ρ 1)
  let base :=
    gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 1)) (ρ 0) (ρ 1) Ri Rj
  let marginal :=
    gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1)) (ρ 0) (ρ 1)
  have hWi :
      gn21ScaledStateEarning (μ 0) (arrival 0) (multiplicativePricing (m 0)) (ρ 0) =
        Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 0) (arrival 0) Ri (multiplicativePricing (m 0)) (ρ 0)
      harrival0_pos hρ0_meas hρ0_subset rfl
  have hWj :
      gn21ScaledStateEarning (μ 1) (arrival 1) (multiplicativePricing (m 1)) (ρ 1) =
        Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (μ 1) (arrival 1) Rj (multiplicativePricing (m 1)) (ρ 1)
      harrival1_pos hρ1_meas hρ1_subset rfl
  have hbranch_optimal :
      ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
        lemma5MarginalSetReward (μ 1) marginal σ ≤
          lemma5MarginalSetReward (μ 1) marginal (ρ 1) := by
    intro σ hσ hmeas
    dsimp [marginal]
    exact lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_one
      μ arrival switch12 switch21 (fun i => multiplicativePricing (m i)) hρ_meas
      harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hq1 hw1 htime1_all
      σ hσ hmeas
  have hmarginal_integrable : IntegrableOn marginal acceptAllPolicy (μ 1) := by
    dsimp [marginal]
    exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
      (ρ 0) (ρ 1) acceptAllPolicy
      (hq1 acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      (hw1 acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
      (htime1_all acceptAllPolicy (fun _ hτ => hτ) measurableSet_acceptAllPolicy)
  have hRi_lt_Rj : Ri < Rj := by
    dsimp [Ri, Rj]
    exact gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      μ arrival switch12 switch21 (fun i => multiplicativePricing (m i))
      harrival0_pos harrival1_pos hswitch12_pos hswitch21_pos hsurge hρ
  have hbase_cont : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    exact continuousOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 1) Ri Rj
      (ρ 0) (ρ 1)
  have hbase_mono : StrictMonoOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictMonoOn_gn21MeasuredRightLemma6ResponseAtCurrent_multiplicative
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21 (m 1) Ri Rj
      (ρ 0) (ρ 1) hRi_lt_Rj hswitch21_pos hsum1
  have hnegative_transfer :
      ∀ τ : TripLength, 0 < τ → base τ < 0 → marginal τ < 0 := by
    intro τ hτ hbase_neg
    have hscale_pos :
        0 < gn21MeasuredRightLemma6ScaleAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) τ :=
      gn21MeasuredRightLemma6ScaleAtCurrent_pos (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1)
        hQ0_pos hT0_pos hT1_pos hden_pos hτ
    have hscale_eq :
        marginal τ =
          gn21MeasuredRightLemma6ScaleAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) τ * base τ := by
      dsimp [marginal, base]
      exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (multiplicativePricing (m 0)) (multiplicativePricing (m 1))
        (ρ 0) (ρ 1) Ri Rj τ (ne_of_gt hden_pos) (ne_of_gt hτ)
        (ne_of_gt hT0_pos) (ne_of_gt hT1_pos) hWi hWj
    rw [hscale_eq]
    exact mul_neg_of_pos_of_neg hscale_pos hbase_neg
  rcases lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_optimal
      (μ 1) base marginal (ρ 1) hρ1_meas hρ1_subset hmass hmarginal_integrable
      hbranch_optimal hnegative_transfer hbase_cont hbase_mono with hpositive | ⟨t, ht, hzero⟩
  · left
    simpa [base, Ri, Rj] using hpositive
  · right
    exact ⟨t, ht, by simpa [base, Ri, Rj] using hbase_mono,
      by simpa [base, Ri, Rj] using hzero⟩

/--
Positive-mass measurable optimality is locally optimal against one-state
replacements that stay in the positive-mass measurable source domain.
-/
theorem dynamicStateReward_optimal_of_dynamicPositiveMassMeasurableOptimal
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicPositiveMassMeasurableOptimal μ R σ) (i : Fin 2)
    {τ : TripPolicy}
    (hτ :
      dynamicFeasibleMeasurablePositiveMassPolicy μ
        (Function.update σ i τ)) :
    dynamicStateReward R σ i τ ≤ dynamicStateReward R σ i (σ i) := by
  unfold dynamicStateReward
  simpa [Function.update_eq_self] using
    hσ.2 (Function.update σ i τ) hτ

/--
Positive-mass measurable optimality is locally optimal against replacing one
state by accept-all, provided accept-all has positive mass in each state.
-/
theorem dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicPositiveMassMeasurableOptimal μ R σ)
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (i : Fin 2) :
    dynamicStateReward R σ i acceptAllPolicy ≤
      dynamicStateReward R σ i (σ i) :=
  dynamicStateReward_optimal_of_dynamicPositiveMassMeasurableOptimal μ R hσ i
    (dynamicFeasibleMeasurablePositiveMassPolicy_update_acceptAll
      hσ.1 hmass_acceptAll i)

/--
Positive-mass measurable optimality for the measured GN21 reward is preserved
when the surge-state policy is replaced by exact accept-all after it has been
shown accept-all almost everywhere.
-/
theorem dynamicPositiveMassMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_one_acceptAll_of_ae
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicPositiveMassMeasurableOptimal μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (hae : acceptAllAlmostEverywhere (μ 1) (ρ 1)) :
    dynamicPositiveMassMeasurableOptimal μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
      (Function.update ρ 1 acceptAllPolicy) := by
  have hpolicy_ae :
      policyAlmostEverywhereEq (μ 1) (ρ 1) acceptAllPolicy :=
    policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
      (μ 1) (hρ.1.1 1).1 hae
  constructor
  · exact
      dynamicFeasibleMeasurablePositiveMassPolicy_update_acceptAll
        hρ.1 hmass_acceptAll 1
  · intro κ hκ
    have heq :=
      gn21MeasuredDynamicRewardFunctional_congr_right_policy_ae
        μ arrival switch12 switch21 w hpolicy_ae
    simpa [← heq] using hρ.2 κ hκ

/--
Local non-surge accept-all marginal comparison from a one-state dynamic reward
comparison.  This is the algebraic core of
`lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero`
with the global measurable-optimality premise replaced by the exact local
accept-all replacement inequality.
-/
theorem lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hlocal :
      dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 0 acceptAllPolicy ≤
        dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 0 (ρ 0))
    (harrival_pos : 0 < arrival 0)
    (Hcurrent :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (HacceptAll :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 acceptAllPolicy (ρ 1))
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hden_acceptAll_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
          gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
    (hq_integrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hw_integrable_acceptAll : IntegrableOn (w 0) acceptAllPolicy (μ 0))
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq_integrable_current :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        (ρ 0) (μ 0))
    (hw_integrable_current : IntegrableOn (w 0) (ρ 0) (μ 0))
    (htime_integrable_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 0) (μ 0)) :
    lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) acceptAllPolicy ≤
      lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) (ρ 0) := by
  have hdyn :
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1) ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero]
      using hlocal
  have hagg :
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1) ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) acceptAllPolicy (ρ 1) HacceptAll,
      paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) Hcurrent] at hdyn
    exact hdyn
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy)
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) acceptAllPolicy)
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) ≤
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) := by
    simpa [gn21MeasuredAggregateRewardPrimitives] using hagg
  have hlinear_raw :=
    gn21AggregateDynamicReward_candidate_left_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
        acceptAllPolicy)
      (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) acceptAllPolicy)
      hden_pos hden_acceptAll_pos hquot
  have hlinear :
      gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          acceptAllPolicy ≤
        gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          (ρ 0) := by
    simpa [gn21MeasuredLeftLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy
      hq_integrable_acceptAll hw_integrable_acceptAll
      htime_integrable_acceptAll
  have hscore_current :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) (ρ 0)
      hq_integrable_current hw_integrable_current htime_integrable_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith [harrival_pos, hlinear]

/--
Surge-state counterpart of
`lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward`.
-/
theorem lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_one_of_local_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hlocal :
      dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 1 acceptAllPolicy ≤
        dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 1 (ρ 1))
    (harrival_pos : 0 < arrival 1)
    (Hcurrent :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (HacceptAll :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) acceptAllPolicy)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hden_acceptAll_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (ρ 0) *
          gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hq_integrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hw_integrable_acceptAll : IntegrableOn (w 1) acceptAllPolicy (μ 1))
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq_integrable_current :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        (ρ 1) (μ 1))
    (hw_integrable_current : IntegrableOn (w 1) (ρ 1) (μ 1))
    (htime_integrable_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 1) (μ 1)) :
    lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) acceptAllPolicy ≤
      lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) (ρ 1) := by
  have hdyn :
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one]
      using hlocal
  have hagg :
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) acceptAllPolicy HacceptAll,
      paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) Hcurrent] at hdyn
    exact hdyn
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) acceptAllPolicy) ≤
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) := by
    simpa [gn21MeasuredAggregateRewardPrimitives] using hagg
  have hlinear_raw :=
    gn21AggregateDynamicReward_candidate_right_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
        acceptAllPolicy)
      (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) acceptAllPolicy)
      hden_pos hden_acceptAll_pos hquot
  have hlinear :
      gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          acceptAllPolicy ≤
        gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          (ρ 1) := by
    simpa [gn21MeasuredRightLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy
      hq_integrable_acceptAll hw_integrable_acceptAll
      htime_integrable_acceptAll
  have hscore_current :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) (ρ 1)
      hq_integrable_current hw_integrable_current htime_integrable_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith [harrival_pos, hlinear]

/-- Zero accepted mass on a finite-measure policy makes accepted trip time vanish. -/
theorem singleStateTripTime_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripTime μ σ = 0 :=
  singleStateTripTime_eq_zero_of_measure_zero μ σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/-- Zero accepted mass on a finite-measure policy makes accepted payment vanish. -/
theorem singleStateTripPayment_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {w : PricingFunction} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripPayment μ w σ = 0 :=
  singleStateTripPayment_eq_zero_of_measure_zero μ w σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/--
Zero accepted mass on a finite-measure policy gives zero scaled earning in the
cancellation-preserving Appendix-D primitives.
-/
theorem gn21ScaledStateEarning_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {w : PricingFunction} {σ : TripPolicy}
    (arrivalRate : ℝ)
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    gn21ScaledStateEarning μ arrivalRate w σ = 0 :=
  gn21ScaledStateEarning_eq_zero_of_measure_zero μ arrivalRate w σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/--
At a finite-measure zero-mass endpoint, the displayed state-rate convention is
zero because the accepted-payment numerator vanishes.
-/
theorem gn21MeasuredStateRewardRate_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {w : PricingFunction} {σ : TripPolicy}
    (arrivalRate : ℝ)
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ = 0 :=
  gn21MeasuredStateRewardRate_eq_zero_of_payment_zero μ arrivalRate w σ
    (singleStateTripPayment_eq_zero_of_mass_zero_of_ne_top hmass hfinite)

/-- The paper's real-valued state cycle time totalizes to zero at zero mass. -/
theorem gn21StateCycleTime_eq_zero_of_mass_time_zero
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0) :
    gn21StateCycleTime μ arrivalRate σ = 0 := by
  simp [gn21StateCycleTime, hmass, htime]

/-- The paper's real-valued state reward rate totalizes to zero at zero mass/payment/time. -/
theorem gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0)
    (hpayment : singleStateTripPayment μ w σ = 0) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ = 0 := by
  simp [gn21MeasuredStateRewardRate, gn21StateRewardRate,
    gn21StateMeanEarning, gn21StateCycleTime, hmass, htime, hpayment]

/--
If both states have zero accepted mass, zero accepted time, and zero accepted
payment, the current real-valued measured dynamic reward totalizes to zero.
-/
theorem gn21MeasuredDynamicReward_eq_zero_of_both_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ = 0 := by
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    gn21MeasuredTimeFraction, gn21TimeFractionFormula,
    gn21MeasuredStateRewardRate, gn21StateRewardRate, gn21StateMeanEarning,
    gn21StateCycleTime, hmassI, hmassJ, htimeI, htimeJ, hpaymentI,
    hpaymentJ]

/--
With the current real-valued totalization, if the left state has zero accepted
mass/time/payment and the right-state time-fraction denominator is nonzero,
the measured dynamic reward collapses to the right state's reward rate.  This
is why full-domain Theorem 3 needs an explicit zero-mass dominance or a
different extended-real reward model.
-/
theorem gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ σJ *
            gn21StateCycleTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ := by
  have hleft_fraction :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ = 0 := by
    simp [gn21MeasuredTimeFraction, gn21TimeFractionFormula,
      gn21StateCycleTime, hmassI, htimeI]
  have hright_fraction :
      gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
        σJ σI = 1 := by
    have hcycleI :
        gn21StateCycleTime μI arrivalI σI = 0 :=
      gn21StateCycleTime_eq_zero_of_mass_time_zero
        μI arrivalI σI hmassI htimeI
    unfold gn21MeasuredTimeFraction gn21TimeFractionFormula
    rw [hcycleI, hmassI]
    set A :=
      arrivalJ * singleStateTripMass μJ σJ *
        gn21StateCycleTime μJ arrivalJ σJ *
          gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI
    have hden_eq :
        arrivalI * 0 * 0 *
              gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ +
            A = A := by
      ring
    rw [hden_eq]
    exact div_self (by simpa [A] using hdenJ)
  have hleft_reward :
      gn21MeasuredStateRewardRate μI arrivalI wI σI = 0 :=
    gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
      μI arrivalI wI σI hmassI htimeI hpaymentI
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    hleft_fraction, hright_fraction, hleft_reward]

/-- State-swapped one-zero-state simplification. -/
theorem gn21MeasuredDynamicReward_eq_left_rewardRate_of_right_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0)
    (hdenI :
      arrivalI * singleStateTripMass μI σI *
            gn21StateCycleTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μI arrivalI wI σI := by
  have hswap :=
    gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
      μJ μI arrivalJ arrivalI switchJI switchIJ wJ wI σJ σI
      hmassJ htimeJ hpaymentJ hdenI
  simpa [gn21MeasuredDynamicReward, gn21DynamicRewardFormula, add_comm,
    mul_comm] using hswap

/--
Concrete zero-mass obstruction: if the left state accepts no trips and the
right state accepts all trips, the current real-valued measured reward
totalizes to the right state's reward rate whenever the right-state
time-fraction denominator is nonzero.
-/
theorem gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_empty_acceptAll
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ (∅ : TripPolicy) acceptAllPolicy =
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy :=
    gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ
      (∅ : TripPolicy) acceptAllPolicy
      (by simp [singleStateTripMass])
      (by simp [singleStateTripTime])
      (by simp [singleStateTripPayment])
      hdenJ

/--
If the right accept-all state reward rate is strictly larger than the full
accept-all dynamic reward, the left-empty/right-accept-all policy is a
profitable deviation under the current real-valued totalization.  This records
why a full-domain Theorem 3 cannot be obtained from the positive-mass source
proof without an explicit zero-mass dominance condition or a revised reward
interface.
-/
theorem gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_right_rewardRate_gt
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0)
    (hgt :
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
          wI wJ acceptAllPolicy acceptAllPolicy <
        gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ (∅ : TripPolicy) acceptAllPolicy := by
  rw [gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_empty_acceptAll
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ hdenJ]
  exact hgt

/--
If the two accept-all state reward rates are `R1 < R2` and the left state has
positive accept-all time share, then accept-all's dynamic reward is strictly
below the right accept-all state reward rate.  This is the weighted-average
algebra behind the zero-mass boundary obstruction.
-/
theorem gn21MeasuredDynamicReward_acceptAll_lt_right_rewardRate_of_state_rates
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (R1 R2 : ℝ)
    (hleft_rate :
      gn21MeasuredStateRewardRate μI arrivalI wI acceptAllPolicy = R1)
    (hright_rate :
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy = R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
          acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
            acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
            acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy := by
  rw [paper_lemma1_measured_dynamic_reward_decomposition, hleft_rate,
    hright_rate]
  exact weightedAverage_lt_right_of_left_lt_right hleft_fraction_pos
    hfractions_sum hR1_lt_R2

/--
Sharper zero-mass obstruction for the Theorem 3 accept-all accounting shape:
when accept-all has state rates `R1 < R2` and a positive left-state time share,
the left-empty/right-accept-all zero-mass policy strictly improves on
accept-all under the current real-valued reward totalization.
-/
theorem gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_state_rates
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (R1 R2 : ℝ)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0)
    (hleft_rate :
      gn21MeasuredStateRewardRate μI arrivalI wI acceptAllPolicy = R1)
    (hright_rate :
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy = R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
          acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
            acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
            acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ (∅ : TripPolicy) acceptAllPolicy :=
  gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_right_rewardRate_gt
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ hdenJ
    (gn21MeasuredDynamicReward_acceptAll_lt_right_rewardRate_of_state_rates
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ R1 R2 hleft_rate
      hright_rate hleft_fraction_pos hfractions_sum hR1_lt_R2)

/--
A feasible measurable profitable deviation refutes measurable incentive
compatibility.  This is the measurable-domain counterpart of the full-domain
profitable-deviation negation used elsewhere in the GN21 development.
-/
theorem not_dynamicMeasurableIncentiveCompatible_of_feasible_profitableDeviation
    {R : DynamicReward} {ρ : Fin 2 → TripPolicy}
    (hρ : dynamicFeasibleMeasurablePolicy ρ)
    (hdev : R acceptAllDynamicPolicy < R ρ) :
    ¬ dynamicMeasurableIncentiveCompatible R := by
  intro hIC
  exact not_le_of_gt hdev (hIC.2 ρ hρ)

/--
Structured Theorem 3 zero-mass boundary, state-rate form: for the CTMC pricing
surface used in the theorem statement, if the right accept-all state reward
rate exceeds the left accept-all state reward rate and the left state has
positive accept-all time share, then the left-empty/right-accept-all feasible
measurable policy strictly improves on accept-all under the current real-valued
reward totalization.
-/
theorem gn21MeasuredCTMCStructuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_state_rates
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 R1 R2 : ℝ)
    (hdenJ :
      arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy *
            gn21StateCycleTime (μ 1) (arrival 1) acceptAllPolicy *
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              (∅ : TripPolicy) ≠ 0)
    (hleft_rate :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        R1)
    (hright_rate :
      gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction (μ 1) (μ 0) (arrival 1) (arrival 0)
            switch21 switch12 acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12 switch21 m z
        acceptAllDynamicPolicy <
      gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12 switch21 m z
        (Function.update acceptAllDynamicPolicy 0 (∅ : TripPolicy)) := by
  have hraw :=
    gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_state_rates
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
      R1 R2 hdenJ hleft_rate hright_rate hleft_fraction_pos
      hfractions_sum hR1_lt_R2
  simpa [gn21MeasuredCTMCStructuredDynamicReward,
    gn21MeasuredDynamicRewardFunctional, acceptAllDynamicPolicy,
    Function.update] using hraw

/--
Structured Theorem 3 zero-mass obstruction against full measurable IC: the
state-rate configuration above makes the left-empty/right-accept-all policy a
feasible measurable profitable deviation, so accept-all is not measurable
incentive compatible for the current real-valued totalization.
-/
theorem not_dynamicMeasurableIncentiveCompatible_gn21MeasuredCTMCStructuredDynamicReward_of_left_empty_acceptAll_state_rates
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 R1 R2 : ℝ)
    (hdenJ :
      arrival 1 * singleStateTripMass (μ 1) acceptAllPolicy *
            gn21StateCycleTime (μ 1) (arrival 1) acceptAllPolicy *
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              (∅ : TripPolicy) ≠ 0)
    (hleft_rate :
      gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          acceptAllPolicy =
        R1)
    (hright_rate :
      gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          acceptAllPolicy =
        R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction (μ 1) (μ 0) (arrival 1) (arrival 0)
            switch21 switch12 acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    ¬ dynamicMeasurableIncentiveCompatible
      (gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12 switch21 m z) := by
  refine
    not_dynamicMeasurableIncentiveCompatible_of_feasible_profitableDeviation
      (ρ := Function.update acceptAllDynamicPolicy 0 (∅ : TripPolicy))
      ?hfeasible ?hdev
  · exact
      dynamicFeasibleMeasurablePolicy_update
        dynamicFeasibleMeasurablePolicy_acceptAll 0 (∅ : TripPolicy)
        (by intro x hx; cases hx)
        (by simp)
  · exact
      gn21MeasuredCTMCStructuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_state_rates
        μ arrival m z switch12 switch21 R1 R2 hdenJ hleft_rate hright_rate
        hleft_fraction_pos hfractions_sum hR1_lt_R2

/-- A feasible measurable dynamic policy has zero accepted mass in some state. -/
def dynamicHasZeroAcceptedMass
    (μ : Fin 2 → Measure TripLength) (σ : Fin 2 → TripPolicy) : Prop := ∃ i : Fin 2, singleStateTripMass (μ i) (σ i) = 0

/--
If no state has zero accepted mass, feasible measurability upgrades to the
positive-mass feasible source domain.
-/
theorem dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hno_zero : ¬ dynamicHasZeroAcceptedMass μ σ) :
    dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  constructor
  · exact hσ
  · intro i
    have hne : singleStateTripMass (μ i) (σ i) ≠ 0 := by
      intro hzero
      exact hno_zero ⟨i, hzero⟩
    exact lt_of_le_of_ne (singleStateTripMass_nonneg (μ i) (σ i))
      (Ne.symm hne)

/-- A feasible measurable policy outside the positive-mass domain has zero mass in some state. -/
theorem dynamicHasZeroAcceptedMass_of_not_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hnot :
      ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ) :
    dynamicHasZeroAcceptedMass μ σ := by
  by_contra hno_zero
  exact hnot
    (dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass hσ
      hno_zero)

/-- A zero-mass state prevents membership in the positive-mass source domain. -/
theorem not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hzero : dynamicHasZeroAcceptedMass μ σ) :
    ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  intro hpos
  rcases hzero with ⟨i, hmass_zero⟩
  have hmass_pos := hpos.2 i
  linarith

/--
Strict-dominance certificate for the boundary omitted by the paper's
positive-mass reward-rate algebra: every feasible measurable zero-mass policy
is strictly dominated by some feasible measurable positive-mass policy.
-/
structure DynamicZeroMassStrictDominanceCertificate
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward) where
  improve_zero_mass :
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy σ →
        dynamicHasZeroAcceptedMass μ σ →
          ∃ τ : Fin 2 → TripPolicy,
            dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ

/--
Build the explicit zero-mass certificate from the often-convenient complement
form: every feasible policy outside the positive-mass domain is dominated by a
positive-mass feasible policy.
-/
def DynamicZeroMassStrictDominanceCertificate.of_not_positive_mass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ →
            ∃ τ : Fin 2 → TripPolicy,
              dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ) :
    DynamicZeroMassStrictDominanceCertificate μ R where
  improve_zero_mass := by
    intro σ hσ hzero
    exact hdom σ hσ
      (not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass hzero)

/--
Build the zero-mass certificate from one fixed positive-mass witness that
strictly dominates every feasible zero-mass policy.
-/
def DynamicZeroMassStrictDominanceCertificate.of_fixed_witness
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (τ : Fin 2 → TripPolicy)
    (hτ : dynamicFeasibleMeasurablePositiveMassPolicy μ τ)
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          dynamicHasZeroAcceptedMass μ σ →
            R σ < R τ) :
    DynamicZeroMassStrictDominanceCertificate μ R where
  improve_zero_mass := by
    intro σ hσ hzero
    exact ⟨τ, hτ, hdom σ hσ hzero⟩

/--
Accept-all specialization of the fixed-witness constructor.  This is the
paper-facing zero-mass route for GN21: after proving accept-all has positive
mass in both states, it remains only to prove every feasible zero-mass policy
has lower total reward than accept-all under the chosen reward interface.
-/
def DynamicZeroMassStrictDominanceCertificate.of_acceptAll_dominates_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          dynamicHasZeroAcceptedMass μ σ →
            R σ < R acceptAllDynamicPolicy) :
    DynamicZeroMassStrictDominanceCertificate μ R :=
  DynamicZeroMassStrictDominanceCertificate.of_fixed_witness
    acceptAllDynamicPolicy
    (dynamicFeasibleMeasurablePositiveMassPolicy_acceptAll hmass_acceptAll)
    hdom

/--
If a feasible zero-mass policy strictly beats accept-all while accept-all is
already optimal on the positive-mass source domain, then no zero-mass strict
dominance certificate can exist.  This records the logical obstruction behind
the GN21 totalized-reward boundary.
-/
theorem not_DynamicZeroMassStrictDominanceCertificate_of_zero_mass_policy_beats_acceptAll
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σ : Fin 2 → TripPolicy}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hσ_zero : dynamicHasZeroAcceptedMass μ σ)
    (hgt : R acceptAllDynamicPolicy < R σ) :
    ¬ DynamicZeroMassStrictDominanceCertificate μ R := by
  intro hzero
  rcases hzero.improve_zero_mass σ hσ hσ_zero with
    ⟨τ, hτ_pos, hσ_lt_τ⟩
  have hτ_le_accept : R τ ≤ R acceptAllDynamicPolicy := hposIC.2 τ hτ_pos
  linarith

/--
A dynamic reward whose value is defined only on the denominator-valid
positive-mass feasible source domain.
-/
structure DynamicDefinedReward
    (μ : Fin 2 → Measure TripLength) where
  value :
    (σ : Fin 2 → TripPolicy) →
      dynamicFeasibleMeasurablePositiveMassPolicy μ σ → ℝ

/-- The optional value of a defined reward at an arbitrary dynamic policy. -/
noncomputable def DynamicDefinedReward.value?
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ)
    (σ : Fin 2 → TripPolicy) : Option ℝ := by
  classical
  exact
    if hσ : dynamicFeasibleMeasurablePositiveMassPolicy μ σ then
      some (R.value σ hσ)
    else
      none

/-- Order an optional reward value against a real benchmark. -/
def optionRewardLe (x : Option ℝ) (y : ℝ) : Prop := ∀ r : ℝ, x = some r → r ≤ y

/--
Defined-reward measurable optimality: the target is positive-mass feasible, and
every feasible measurable policy with a defined positive-mass reward is no
better than the target.  Feasible zero-mass policies have no reward value here
rather than a totalized real quotient value.
-/
def dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ)
    (σstar : Fin 2 → TripPolicy) : Prop :=
  ∃ hstar : dynamicFeasibleMeasurablePositiveMassPolicy μ σstar,
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy σ →
        optionRewardLe (R.value? σ) (R.value σstar hstar)

/--
Defined-reward measurable IC: accepting all trips is optimal for the partial
reward surface.
-/
def dynamicDefinedMeasurableIncentiveCompatible
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ) : Prop := dynamicDefinedMeasurableOptimal R acceptAllDynamicPolicy

/-- View an ordinary total dynamic reward as a reward defined on positive-mass policies. -/
def DynamicDefinedReward.of_total
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) : DynamicDefinedReward μ where
  value := fun σ _hσ => R σ

/--
Positive-mass measurable optimality immediately gives defined-reward optimality
for any partial reward interface that agrees with the total reward on the
positive-mass source domain.
-/
theorem dynamicDefinedMeasurableOptimal_of_positiveMass_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    {σstar : Fin 2 → TripPolicy}
    (hposOpt : dynamicPositiveMassMeasurableOptimal μ Rtot σstar)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicDefinedMeasurableOptimal Rdef σstar := by
  classical
  refine ⟨hposOpt.1, ?_⟩
  intro σ _hσ r hr
  by_cases hσ_pos : dynamicFeasibleMeasurablePositiveMassPolicy μ σ
  · have hr' : some (Rdef.value σ hσ_pos) = some r := by
      simpa [DynamicDefinedReward.value?, hσ_pos] using hr
    have hreq : Rdef.value σ hσ_pos = r := Option.some.inj hr'
    rw [← hreq]
    rw [hagree σ hσ_pos, hagree σstar hposOpt.1]
    exact hposOpt.2 σ hσ_pos
  · simpa [DynamicDefinedReward.value?, hσ_pos] using hr

/--
Positive-mass measurable optimality immediately gives defined-reward optimality
for the corresponding total reward viewed through the partial interface.
-/
theorem dynamicDefinedMeasurableOptimal_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σstar : Fin 2 → TripPolicy}
    (hposOpt : dynamicPositiveMassMeasurableOptimal μ R σstar) :
    dynamicDefinedMeasurableOptimal
      (DynamicDefinedReward.of_total μ R) σstar :=
  dynamicDefinedMeasurableOptimal_of_positiveMass_agree hposOpt
    (by intro σ hσ; rfl)

/--
Positive-mass measurable IC immediately gives defined-reward IC for any partial
reward interface that agrees with the total reward on the positive-mass source
domain.
-/
theorem dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ Rtot)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicDefinedMeasurableIncentiveCompatible Rdef := dynamicDefinedMeasurableOptimal_of_positiveMass_agree hposIC hagree

/--
Positive-mass measurable IC immediately gives defined-reward IC for the
corresponding partial reward interface.  This is the source-faithful alternative
to assigning arbitrary totalized real values to zero-mass denominator failures.
-/
theorem dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R) :
    dynamicDefinedMeasurableIncentiveCompatible
      (DynamicDefinedReward.of_total μ R) :=
  dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass_agree hposIC
    (by intro σ hσ; rfl)

/--
A defined-reward optimum whose partial reward agrees with a total reward is also
a positive-mass optimum for that total reward.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    {σstar : Fin 2 → TripPolicy}
    (hdefOpt :
      dynamicDefinedMeasurableOptimal Rdef σstar)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicPositiveMassMeasurableOptimal μ Rtot σstar := by
  classical
  rcases hdefOpt with ⟨hstar_pos, hle⟩
  refine ⟨hstar_pos, ?_⟩
  intro σ hσ_pos
  have hle_def :
      Rdef.value σ hσ_pos ≤ Rdef.value σstar hstar_pos :=
    hle σ hσ_pos.1 (Rdef.value σ hσ_pos) (by
      simp [DynamicDefinedReward.value?, hσ_pos])
  rwa [hagree σ hσ_pos, hagree σstar hstar_pos] at hle_def

/--
A defined-reward optimum for a total reward viewed partially is also a
positive-mass optimum for the original reward.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σstar : Fin 2 → TripPolicy}
    (hdefOpt :
      dynamicDefinedMeasurableOptimal
        (DynamicDefinedReward.of_total μ R) σstar) :
    dynamicPositiveMassMeasurableOptimal μ R σstar :=
  dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal_agree
    hdefOpt (by intro σ hσ; rfl)

/--
Positive-mass a.e. uniqueness transfers to defined-reward optima for the same
total reward viewed through the partial reward interface.
-/
theorem dynamicAcceptAllAlmostEverywhere_of_dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ)
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicDefinedMeasurableOptimal
        (DynamicDefinedReward.of_total μ R) ρ) :
    dynamicAcceptAllAlmostEverywhere μ ρ :=
  hAE ρ
    (dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal
      hρ)

/--
Positive-mass measurable IC lifts to full feasible-measurable IC once every
zero-mass feasible policy is strictly dominated by a positive-mass feasible
policy.
-/
theorem dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R := by
  constructor
  · exact hposIC.1.1
  · intro σ hσ
    by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
    · rcases hzero.improve_zero_mass σ hσ hσ_zero with
        ⟨τ, hτ_pos, hlt⟩
      have hτ_le_accept :
          R τ ≤ R acceptAllDynamicPolicy := hposIC.2 τ hτ_pos
      linarith
    · have hσ_pos :
          dynamicFeasibleMeasurablePositiveMassPolicy μ σ :=
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ hσ_zero
      exact hposIC.2 σ hσ_pos

/--
A full feasible-measurable optimum belongs to the positive-mass source domain
under the same zero-mass strict-dominance certificate.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σ : Fin 2 → TripPolicy}
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R)
    (hσ : dynamicMeasurableOptimal R σ) :
    dynamicPositiveMassMeasurableOptimal μ R σ := by
  by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
  · rcases hzero.improve_zero_mass σ hσ.1 hσ_zero with
      ⟨τ, hτ_pos, hlt⟩
    have hτ_le_σ : R τ ≤ R σ := hσ.2 τ hτ_pos.1
    linarith
  · constructor
    · exact
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ.1 hσ_zero
    · intro τ hτ_pos
      exact hσ.2 τ hτ_pos.1

/--
Positive-mass measurable IC plus positive-mass a.e. uniqueness lifts to the
full feasible-measurable a.e.-unique conclusion under zero-mass strict
dominance.
-/
theorem dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hposAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine
    ⟨dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
      hposIC hzero, ?_⟩
  intro ρ hρ
  exact hposAE ρ
    (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
      hzero hρ)

/--
Positive-mass analogue of the measurable positive-response marginal
certificate.  This is the same Lemma-5 endpoint as the full certificate, but
the optimizers quantified over are restricted to the nondegenerate source
domain where the Appendix-D reward-rate formulas are defined.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 0) response τ ≤
                lemma5MarginalSetReward (μ 0) response (ρ 0))
  surge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 1) response τ ≤
                lemma5MarginalSetReward (μ 1) response (ρ 1))

/--
Positive-response marginal optimality gives a.e. accept-all uniqueness inside
the positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive hoptimal
  · rcases C.surge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive hoptimal

/--
Positive-mass analogue of the accept-all-candidate positive-response
certificate.  This weaker Lemma-5 interface is enough for a.e. uniqueness and
only compares each positive-mass optimum with the accept-all candidate.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 0) response (ρ 0)
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)

/--
Accept-all candidate comparisons give a.e. accept-all uniqueness inside the
positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive (by simpa [hpositive_eq] using hcandidate)
  · rcases C.surge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive (by simpa [hpositive_eq] using hcandidate)

/--
Candidate-only version of the positive-mass positive-response certificate.
This omits accept-all optimality because Theorem 3's positive-mass IC
construction can supply that separately; for a.e. uniqueness, the proof only
needs the statewise accept-all candidate comparisons.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  nonsurge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 0) response (ρ 0)
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)

/--
Candidate comparisons alone give a.e. accept-all uniqueness for positive-mass
measurable optima.
-/
theorem positiveMassMeasurable_acceptAll_ae_unique_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate
        μ R) :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        dynamicAcceptAllAlmostEverywhere μ ρ := by
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive (by simpa [hpositive_eq] using hcandidate)
  · rcases C.surge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive (by simpa [hpositive_eq] using hcandidate)

/--
Sequential positive-response certificate for the paper's Theorem 3 route.  It
first proves the surge state is accept-all a.e. at the current fixed non-surge
policy; after that rewrite, the non-surge Lemma 10 comparison is only required
with the surge state fixed at exact accept-all.
-/
structure Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)
  nonsurge_after_surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        acceptAllAlmostEverywhere (μ 1) (ρ 1) →
          ∃ response : TripLength → ℝ,
            Measurable response ∧
              IntegrableOn response acceptAllPolicy (μ 0) ∧
              lemma5PolicyForm .positive
                (lemma5PositiveResponsePolicy response) ∧
              lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
                lemma5MarginalSetReward (μ 0) response (ρ 0)

/--
Sequential statewise candidate comparisons give a.e. accept-all uniqueness in
the positive-mass measurable source domain.
-/
theorem positiveMassMeasurable_acceptAll_ae_unique_of_sequential_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate
        μ R) :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        dynamicAcceptAllAlmostEverywhere μ ρ := by
  intro ρ hρ
  rcases C.surge_acceptAll_candidate ρ hρ with
    ⟨response1, hmeas1, hint1, hpositive1, hcandidate1⟩
  have hpositive1_eq :
      lemma5PositiveResponsePolicy response1 = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response1)
      hpositive1
  have hsurge :
      acceptAllAlmostEverywhere (μ 1) (ρ 1) :=
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 1) response1 (ρ 1) hmeas1 hint1 (hρ.1.1 1).2 (hρ.1.1 1).1
      hpositive1 (by simpa [hpositive1_eq] using hcandidate1)
  rcases C.nonsurge_after_surge_acceptAll_candidate ρ hρ hsurge with
    ⟨response0, hmeas0, hint0, hpositive0, hcandidate0⟩
  have hpositive0_eq :
      lemma5PositiveResponsePolicy response0 = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response0)
      hpositive0
  have hnonsurge :
      acceptAllAlmostEverywhere (μ 0) (ρ 0) :=
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 0) response0 (ρ 0) hmeas0 hint0 (hρ.1.1 0).2 (hρ.1.1 0).1
      hpositive0 (by simpa [hpositive0_eq] using hcandidate0)
  intro i
  fin_cases i
  · exact hnonsurge
  · exact hsurge

/--
Positive-mass Theorem 3 marginal-response certificate.  This is the source
Theorem 4/Lemma 5 boundary restricted to the denominator-valid domain: after
Theorem 3 constructs `m,z`, every positive-mass measurable optimum has the
positive marginal-response data needed for a.e. accept-all uniqueness.
-/
def theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
Positive-mass Theorem 3 candidate-only positive-response certificate.  This
is the weakest Lemma 5 a.e.-uniqueness boundary: after Theorem 3 constructs
`m,z`, every positive-mass measurable optimum has the positive-response
accept-all candidate comparisons in both states.
-/
def theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
Positive-mass Theorem 3 sequential candidate certificate.  This matches the
paper proof order: first prove the surge state is accept-all a.e.; then use
the non-surge Lemma 10 comparison with the surge state fixed at accept-all.
-/
def theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
The canonical positive-mass sequential reward-rate source assumptions supply
the sequential positive-response uniqueness certificate for the prices
constructed by Theorem 3.
-/
noncomputable def theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
      μ arrival R1 R2 switch12 switch21 := by
  intro m z hsigns hparams
  let P : Theorem3AcceptAllStructuredParameterData
      μ arrival R1 R2 switch12 switch21 m z :=
    Theorem3AcceptAllStructuredParameterData.of_evidence hparams
  let w : Fin 2 → PricingFunction :=
    ctmcStructuredDynamicSurgePrice m z switch12 switch21
  let R : DynamicReward :=
    gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w
  have hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy := by
    intro i
    fin_cases i
    · exact A.hmass1_pos
    · exact A.hmass2_pos
  have current_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) (ρ 1) (hρ.1.2 0) (hρ.1.2 1) A.harrival1_pos
        A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
        (hρ.1.1 0).2 (hρ.1.1 1).2 (hρ.1.1 0).1 (hρ.1.1 1).1
  have acceptAll_nondegenerate :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        acceptAllPolicy acceptAllPolicy :=
    gn21MeasuredPairNondegenerate_of_positive_measure
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      acceptAllPolicy acceptAllPolicy A.hmass1_pos A.hmass2_pos
      A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
      measurableSet_acceptAllPolicy measurableSet_acceptAllPolicy
      (fun _ hτ => hτ) (fun _ hτ => hτ)
  have nonsurge_current_acceptAll_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρ 0) acceptAllPolicy := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) acceptAllPolicy (hρ.1.2 0) A.hmass2_pos
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos (hρ.1.1 0).2 measurableSet_acceptAllPolicy
        (hρ.1.1 0).1 (fun _ hτ => hτ)
  have surge_acceptAll_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρ 0) acceptAllPolicy := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) acceptAllPolicy (hρ.1.2 0) A.hmass2_pos
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos (hρ.1.1 0).2 measurableSet_acceptAllPolicy
        (hρ.1.1 0).1 (fun _ hτ => hτ)
  refine
    { surge_acceptAll_candidate := ?_
      nonsurge_after_surge_acceptAll_candidate := ?_ }
  · intro ρ hρctmc
    have hρ : dynamicPositiveMassMeasurableOptimal μ R ρ := by
      simpa [R, w, gn21MeasuredCTMCStructuredDynamicReward] using hρctmc
    rcases A.surge_reward_rate_data m z hsigns hparams ρ hρ.1 with
      ⟨R1_current, ratio, DSrr⟩
    have hmassI : singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      ne_of_gt (hρ.1.2 0)
    have harrivalMassI :
        arrival 0 * singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      mul_ne_zero (ne_of_gt A.harrival1_pos) hmassI
    have htimeI_pos :
        0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
        (le_of_lt A.harrival1_pos) (hρ.1.1 0).2 (hρ.1.1 0).1
    have DSsrc :
        GN21SurgeLemma9AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratio
          (ctmcStructuredSurgePrice (m 0) (z 0) switch12 switch21)
          (ρ 0) (ρ 1) :=
      GN21SurgeLemma9AcceptAllAggregateSourceData.of_reward_rate
        hmassI harrivalMassI (ne_of_gt htimeI_pos) DSrr
    let DP :
        GN21SurgeLemma9AcceptAllAggregatePrimitiveData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratio
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ρ 0) (ρ 1) :=
      GN21SurgeLemma9AcceptAllAggregatePrimitiveData.of_source
        (hρ.1.1 0).1 (hρ.1.1 0).2 (hρ.1.1 1).1 (hρ.1.1 1).2
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
        A.htime2_integrable A.hq2_integrable
        (by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using DSsrc)
    let DA := GN21SurgeLemma9AcceptAllAggregateData.of_primitive DP
    let response :=
      gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1)
    refine ⟨response, ?_, ?_, ?_, ?_⟩
    · simpa [response] using
        measurable_gn21MeasuredRightMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1)
          ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
            1).measurable)
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy (μ 1) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
            switch21 switch12 acceptAllPolicy
            A.htime2_integrable A.hq2_integrable
      simpa [response] using
        integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1) acceptAllPolicy A.hq2_integrable
          hw_acceptAll A.htime2_integrable
    · have hTj_pos :
          0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
        gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
          (le_of_lt A.harrival2_pos) (hρ.1.1 1).2 (hρ.1.1 1).1
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
          (ne_of_gt DSsrc.current_mass_pos)
          (ne_of_gt (mul_pos A.harrival2_pos DSsrc.current_mass_pos))
          (ne_of_gt hTj_pos) rfl
      have hfixed_reward_rate :
          gn21ScaledStateEarning (μ 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) =
            R1_current * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
          using DSsrc.fixed_reward_rate
      have hbase :
          Lemma5PositiveResponsePolicyFormData
            (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              (ρ 0) (ρ 1) R1_current Rj) .positive :=
        Lemma5PositiveResponsePolicyFormData.positive
          (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) (ρ 1) R1_current Rj)
          (by
            have hpos :=
              gn21MeasuredRightLemma6ResponseAtCurrent_pos_of_lemma9_current_bounds
                (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
                (m 1) R1_current (z 1) ratio Rj
                (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
                (ρ 0) (ρ 1) DSsrc.bounds DSsrc.z_eq
                DSsrc.m_sub_R1_pos DSsrc.R1_nonneg DA.fixed_time_nonneg
                DA.fixed_exit_pos DA.switch_pos DA.switch_sum_pos
                DA.switch_lt_current_exit DA.current_gap_nonneg
                DP.time_integrable_current DP.q_integrable_current
                htimeI_pos hTj_pos hfixed_reward_rate hWj
            intro τ hτ
            simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
              using hpos τ hτ)
      have hscaled :
          Lemma5PositiveResponsePolicyFormData response .positive := by
        simpa [response] using
          gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) (ρ 1) R1_current Rj hbase DA.fixed_exit_pos htimeI_pos
            hTj_pos DA.denominator_pos hfixed_reward_rate hWj
      exact hscaled.policy_form
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy (μ 1) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
            switch21 switch12 acceptAllPolicy
            A.htime2_integrable A.hq2_integrable
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
          switch21 switch12 acceptAllPolicy (le_of_lt A.harrival2_pos)
          A.hswitch21_pos (by linarith [A.hswitch12_pos, A.hswitch21_pos])
          measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      have hT_acceptAll_pos :
          0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
        gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
          acceptAllPolicy (le_of_lt A.harrival2_pos)
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
          DA.fixed_exit_pos hQ_acceptAll_pos htimeI_pos hT_acceptAll_pos
      have hlocal :=
        dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
          μ R hρ hmass_acceptAll 1
      simpa [response, R, w] using
        lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_one_of_local_reward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
          hlocal A.harrival2_pos (current_nondegenerate ρ hρ)
          (surge_acceptAll_nondegenerate ρ hρ)
          DA.denominator_pos hden_acceptAll_pos A.hq2_integrable
          hw_acceptAll A.htime2_integrable DP.q_integrable_current
          hw_current DP.time_integrable_current
  · intro ρ hρctmc hsurgeAE
    have hρ : dynamicPositiveMassMeasurableOptimal μ R ρ := by
      simpa [R, w, gn21MeasuredCTMCStructuredDynamicReward] using hρctmc
    let ρA : Fin 2 → TripPolicy := Function.update ρ 1 acceptAllPolicy
    have hρ_w :
        dynamicPositiveMassMeasurableOptimal μ
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ := by
      simpa [R] using hρ
    have hρA :
        dynamicPositiveMassMeasurableOptimal μ R ρA := by
      have htmp :=
        dynamicPositiveMassMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_one_acceptAll_of_ae
          μ arrival switch12 switch21 w hρ_w hmass_acceptAll hsurgeAE
      simpa [R, ρA] using htmp
    have hsum21 : 0 < switch21 + switch12 := by
      linarith [A.hswitch21_pos, A.hswitch12_pos]
    have hfixed_exit_pos :
        0 <
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy :=
      gn21ExitWeightIntegral_pos_of_switch_pos
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have hfixed_time_pos :
        0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg
        (μ 1) (arrival 1) acceptAllPolicy
        (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
    have hfixed_A_pos :
        0 <
          gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
              switch12 +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
              acceptAllPolicy :=
      add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
        hfixed_exit_pos
    have hfixed_reward_rate :
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy := by
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
                  acceptAllPolicy A.htime2_integrable A.hq2_integrable
        _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
          P.surge_accounting
    have Dsrc :
        ∃ ratio : ℝ,
          GN21NonsurgeLemma10AcceptAllAggregateSourceData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            R2 (z 0) ratio
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) acceptAllPolicy :=
      ⟨P.nonsurgeRatio,
        GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening
          (hρ.1.1 0).1 (hρ.1.1 0).2 A.harrival1_pos
          A.hswitch12_pos A.hswitch21_pos
          (A.htime1_integrable.mono_set (hρ.1.1 0).1)
          (A.hq1_integrable.mono_set (hρ.1.1 0).1)
          A.htime1_integrable A.hq1_integrable
          P.nonsurge_acceptAll_bounds hfixed_A_pos
          (le_of_lt hfixed_exit_pos) (hρ.1.2 0)
          P.hz0 A.hR2_pos hfixed_reward_rate⟩
    rcases Dsrc with ⟨ratio, DN⟩
    let DP :
        GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          R2 (z 0) ratio
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy :=
      GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData.of_source
        (hρ.1.1 0).1 (hρ.1.1 0).2 (fun _ hτ => hτ)
        measurableSet_acceptAllPolicy
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos A.htime1_integrable A.hq1_integrable DN
    let DA := GN21NonsurgeLemma10AcceptAllAggregateData.of_primitive DP
    let response :=
      gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) acceptAllPolicy
    refine ⟨response, ?_, ?_, ?_, ?_⟩
    · simpa [response] using
        measurable_gn21MeasuredLeftMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy
          ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
            0).measurable)
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy (μ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
            switch12 switch21 acceptAllPolicy
            A.htime1_integrable A.hq1_integrable
      simpa [response] using
        integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy acceptAllPolicy A.hq1_integrable
          hw_acceptAll A.htime1_integrable
    · have hTi_pos :
          0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
        gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
          (le_of_lt A.harrival1_pos) (hρ.1.1 0).2 (hρ.1.1 0).1
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
          (ne_of_gt (mul_pos A.harrival1_pos DN.current_mass_pos))
          (ne_of_gt hTi_pos) rfl
      have hbase :
          Lemma5PositiveResponsePolicyFormData
            (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) acceptAllPolicy Ri R2) .positive :=
        Lemma5PositiveResponsePolicyFormData.positive
          (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) acceptAllPolicy Ri R2)
          (by
            have hpos :=
              gn21MeasuredLeftLemma6ResponseAtCurrent_pos_of_lemma10_current_bounds
                (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
                R2 (z 0) ratio Ri
                (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                (ρ 0) acceptAllPolicy DN.bounds DN.z_eq DN.R2_pos
                DA.fixed_exit_pos
                DA.switch_pos DA.switch_sum_pos DA.switch_lt_current_exit
                DA.current_gap_nonneg DA.lower_numerator_pos
                DP.time_integrable_current DP.q_integrable_current
                hTi_pos hfixed_time_pos
                (by
                  simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
                    P.hm0] using hWi)
                DN.fixed_reward_rate
            intro τ hτ
            simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
              P.hm0] using hpos τ hτ)
      have hscaled :
          Lemma5PositiveResponsePolicyFormData response .positive := by
        simpa [response] using
          gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) acceptAllPolicy Ri R2 hbase DA.fixed_exit_pos hTi_pos
            hfixed_time_pos DA.denominator_pos hWi DN.fixed_reward_rate
      exact hscaled.policy_form
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy (μ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
            switch12 switch21 acceptAllPolicy
            A.htime1_integrable A.hq1_integrable
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
        linarith [A.hswitch12_pos, A.hswitch21_pos]
      have hQ_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              acceptAllPolicy :=
        gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0)
          switch12 switch21 acceptAllPolicy (le_of_lt A.harrival1_pos)
          A.hswitch12_pos hsum12 measurableSet_acceptAllPolicy
          (fun _ hτ => hτ)
      have hT_acceptAll_pos :
          0 < gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
        gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0)
          acceptAllPolicy (le_of_lt A.harrival1_pos)
          measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      have hden_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                acceptAllPolicy *
              gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                acceptAllPolicy *
              gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
        gn21AggregateDenominator_pos_of_pos
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy)
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
          (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
          hQ_acceptAll_pos hfixed_exit_pos hT_acceptAll_pos hfixed_time_pos
      have hlocal :=
        dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
          μ R hρA hmass_acceptAll 0
      have HcurrentA :
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρA 0) (ρA 1) := by
        simpa [ρA] using nonsurge_current_acceptAll_nondegenerate ρ hρ
      have HacceptAllA :
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            acceptAllPolicy (ρA 1) := by
        simpa [ρA] using acceptAll_nondegenerate
      simpa [response, R, w, ρA] using
        lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
          hlocal A.harrival1_pos HcurrentA HacceptAllA
          DA.denominator_pos hden_acceptAll_pos A.hq1_integrable
          hw_acceptAll A.htime1_integrable DP.q_integrable_current
          hw_current DP.time_integrable_current

/--
Readable positive-mass source-domain conclusion of Theorem 3 with the paper's
a.e. uniqueness convention restricted to positive-mass measurable optima.
-/
def theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicPositiveMassMeasurableIncentiveCompatible μ
        (gn21MeasuredCTMCStructuredDynamicReward
          μ arrival switch12 switch21 m z) ∧
      (∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/--
Theorem 3 conclusion over the partial defined-reward interface: accept-all is
IC among policies whose positive-mass reward is defined, and every
defined-reward optimum is accept-all a.e.
-/
def theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicDefinedMeasurableIncentiveCompatible
        (DynamicDefinedReward.of_total μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)) ∧
      (∀ ρ : Fin 2 → TripPolicy,
        dynamicDefinedMeasurableOptimal
          (DynamicDefinedReward.of_total μ
            (gn21MeasuredCTMCStructuredDynamicReward
              μ arrival switch12 switch21 m z)) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/-- The positive-mass a.e.-unique conclusion contains the positive-mass IC conclusion. -/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICConclusion_of_ae_unique
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, _hAE, hprice_form, hparams⟩
  exact ⟨m, z, hsigns, hIC, hprice_form, hparams⟩

/--
The positive-mass Theorem 3 endpoint induces the defined-reward Theorem 3
endpoint by leaving zero-mass denominator failures outside the reward domain.
-/
theorem theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩
  exact
    ⟨m, z, hsigns,
      dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass hIC,
      (fun ρ hρ =>
        dynamicAcceptAllAlmostEverywhere_of_dynamicDefinedMeasurableOptimal
          hAE hρ),
      hprice_form, hparams⟩

/--
Add the positive-mass a.e.-unique Theorem 4 conclusion to any compiled
positive-mass Theorem 3 IC construction.  This avoids redoing the scalar
Theorem 3 price construction: the marginal-response certificate is checked
only for the already-constructed `m,z`.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have htheorem4 :
      dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicPositiveMassMeasurableOptimal μ R ρ →
            dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
      μ R (hpositive_marginal m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using htheorem4.2,
    hprice_form, hparams⟩

/--
Add positive-mass a.e. uniqueness to a compiled positive-mass Theorem 3 IC
construction using only the statewise accept-all candidate comparisons.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_acceptAll_candidates
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    positiveMassMeasurable_acceptAll_ae_unique_of_positive_response_acceptAll_candidates
      μ R (hpositive_candidates m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using hAE,
    hprice_form, hparams⟩

/--
Add positive-mass a.e. uniqueness to a compiled positive-mass Theorem 3 IC
construction using the paper-ordered sequential candidate comparisons.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_sequential_positive_response_acceptAll_candidates
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    positiveMassMeasurable_acceptAll_ae_unique_of_sequential_positive_response_acceptAll_candidates
      μ R (hpositive_candidates m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using hAE,
    hprice_form, hparams⟩

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions plus the positive-response
Lemma 5 marginal proof.  The conclusion is exactly the source-domain version
of measurable IC with a.e. accept-all uniqueness: no zero-mass comparison
policy is quantified over.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions_and_positive_response_marginal
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hpositive_marginal

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions plus the weaker
positive-response accept-all candidate comparisons.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions_and_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_acceptAll_candidates
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hpositive_candidates

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions.  This closes the paper-proof
path on the positive-mass source domain: the surge Lemma 9 response is proved
first, the surge state is rewritten to accept-all a.e., and then the non-surge
Lemma 10 response is applied with the surge state fixed at accept-all.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_sequential_positive_response_acceptAll_candidates
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    (theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)

/--
Paper-facing Theorem 3 endpoint over the partial defined-reward interface.  It
uses the same source assumptions as the positive-mass theorem and leaves
zero-mass denominator failures undefined instead of totalizing them as real
reward values.
-/
theorem paper_theorem3_measured_structured_defined_reward_ic_ae_unique_prices_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion_of_positiveMass
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)

/--
Paper-facing domain bridge: a positive-mass a.e.-unique Theorem 3 result lifts
to the full feasible-measurable a.e.-unique result when the constructed prices
also strictly dominate every feasible zero-mass policy.
-/
theorem theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21)
    (hzero :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            DynamicZeroMassStrictDominanceCertificate μ
              (gn21MeasuredCTMCStructuredDynamicReward
                μ arrival switch12 switch21 m z)) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hposIC, hposAE, hprice_form, hparams⟩
  rcases
      dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
        hposIC hposAE (hzero m z hsigns hparams) with
    ⟨hIC, hAE⟩
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

/--
Full feasible-measurable Theorem 3 from the denominator-valid sequential
source assumptions plus the exact zero-mass dominance bridge.  The positive
mass part is the paper-ordered Lemma 9 then Lemma 10 proof; the extra premise
is precisely what is needed to include feasible policies for which the
Appendix-D reward-rate denominators vanish.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_source_assumptions_and_zero_mass_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hzero :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            DynamicZeroMassStrictDominanceCertificate μ
              (gn21MeasuredCTMCStructuredDynamicReward
                μ arrival switch12 switch21 m z)) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hzero

end GN21DriverSurgePricing
