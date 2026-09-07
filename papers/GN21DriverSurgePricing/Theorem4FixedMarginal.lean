import GN21DriverSurgePricing.AffineFixedMarginal
import GN21DriverSurgePricing.CutoffCanonicalization
import GN21DriverSurgePricing.DomainBridge
import GN21DriverSurgePricing.Theorem4AffineAttainment
import GN21DriverSurgePricing.Theorem4WeakAttainment

/-!
# Fixed-marginal Theorem 4 assembly

The source proof of Theorem 4 combines two logically distinct tasks:

* existence of a global optimizer; and
* structural classification of every global optimizer.

`AffineFixedMarginal` proves the second task from the actual Appendix-D
aggregate reward.  This module makes the remaining existence boundary
explicit, and uses aggregate a.e. invariance to select an exact
endpoint-complete source-form optimizer once an optimizer exists.

No theorem in this file uses endpoint derivatives of arbitrary policy unions.
-/

open AppliedModelingLib
open MeasureTheory
open scoped ENNReal

namespace GN21DriverSurgePricing

/--
The fixed-marginal source-form data needed to assemble the structural part of
Theorem 4.  `exists_optimal` is deliberately separate: a coordinatewise
fixed-marginal argument classifies global optima but does not itself prove a
global maximizer exists.
-/
structure GN21Theorem4AggregateFixedMarginalSourceFormData
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape) : Prop where
  exists_optimal :
    exists rho : Fin 2 -> TripPolicy,
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho
  nonsurge_source_form_ae :
    forall rho : Fin 2 -> TripPolicy,
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho ->
      lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0)
  surge_source_form_ae :
    forall rho : Fin 2 -> TripPolicy,
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho ->
      lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1)

/--
Given a true global optimizer and fixed-marginal source-form classifications,
one may select a global optimizer whose two policies are exact source forms.
All global optimizers retain the source forms up to the paper's null-set
convention.
-/
theorem GN21Theorem4AggregateFixedMarginalSourceFormData.assemble
    {mu : Fin 2 -> Measure TripLength}
    {arrival : Fin 2 -> Real}
    {switch12 switch21 : Real}
    {w : Fin 2 -> PricingFunction}
    {shape : Fin 2 -> Lemma5DerivativeShape}
    (D :
      GN21Theorem4AggregateFixedMarginalSourceFormData
        mu arrival switch12 switch21 w shape) :
    (exists rho : Fin 2 -> TripPolicy,
      dynamicMeasurableOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
          rho /\
        lemma5SourcePolicyForm (shape 0) (rho 0) /\
          lemma5SourcePolicyForm (shape 1) (rho 1)) /\
      forall rho : Fin 2 -> TripPolicy,
        dynamicMeasurableOptimal
            (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
            rho ->
          lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
            lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  classical
  rcases D.exists_optimal with ⟨rho0, hrho0⟩
  rcases D.nonsurge_source_form_ae rho0 hrho0 with
    ⟨nonsurgeRepresentative, hnonsurge_form, hnonsurge_ae⟩
  rcases D.surge_source_form_ae rho0 hrho0 with
    ⟨surgeRepresentative, hsurge_form, hsurge_ae⟩
  let rhoStar : Fin 2 -> TripPolicy :=
    Function.update (Function.update rho0 0 nonsurgeRepresentative)
      1 surgeRepresentative
  have hrhoStar_feasible : dynamicFeasibleMeasurablePolicy rhoStar := by
    intro i
    fin_cases i
    · simpa [rhoStar] using
        And.intro
          (lemma5SourcePolicyForm_subset_acceptAll hnonsurge_form)
          (lemma5SourcePolicyForm_measurable hnonsurge_form)
    · simpa [rhoStar] using
        And.intro
          (lemma5SourcePolicyForm_subset_acceptAll hsurge_form)
          (lemma5SourcePolicyForm_measurable hsurge_form)
  have hleft_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho0 =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho0 0 nonsurgeRepresentative) :=
    gn21AggregateDynamicRewardFunctional_congr_left_policy_ae
      mu arrival switch12 switch21 w hnonsurge_ae
  have hsurge_ae_after_left :
      policyAlmostEverywhereEq (mu 1)
        ((Function.update rho0 0 nonsurgeRepresentative) 1)
        surgeRepresentative := by
    simpa using hsurge_ae
  have hright_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho0 0 nonsurgeRepresentative) =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          rhoStar := by
    simpa [rhoStar] using
      (gn21AggregateDynamicRewardFunctional_congr_right_policy_ae
        mu arrival switch12 switch21 w hsurge_ae_after_left)
  have hrhoStar_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho0 =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          rhoStar := hleft_reward.trans hright_reward
  have hrhoStar :
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rhoStar := by
    refine ⟨hrhoStar_feasible, ?_⟩
    intro rho hrho
    rw [← hrhoStar_reward]
    exact hrho0.2 rho hrho
  refine ⟨?_, ?_⟩
  · refine ⟨rhoStar, hrhoStar, ?_, ?_⟩
    · simpa [rhoStar] using hnonsurge_form
    · simpa [rhoStar] using hsurge_form
  · intro rho hrho
    exact ⟨D.nonsurge_source_form_ae rho hrho,
      D.surge_source_form_ae rho hrho⟩

/-!
## Direct aggregate replacement

The compact source-form argument only needs a policy-by-policy weak
replacement, not an endpoint derivative of a policy union.  The next two
lemmas provide that replacement directly from the Appendix-D aggregate
quotient and the fixed-current marginal integral.  They are deliberately
generic in the price functions: affine specialization belongs in the response
analysis, not in the aggregate algebra.
-/

/-- Improving the actual left fixed-current marginal integral weakly improves
the actual Appendix-D aggregate reward. -/
theorem gn21AggregateDynamicRewardFunctional_le_update_left_of_marginal_le
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicFeasibleMeasurablePolicy rho)
    (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_measurable : MeasurableSet candidate)
    (hmarginal :
      lemma5MarginalSetReward (mu 0)
          (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1))
          (rho 0) <=
        lemma5MarginalSetReward (mu 0)
          (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1))
          candidate) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 0 candidate) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hrho0_subset : rho 0 ⊆ acceptAllPolicy := (hrho 0).1
  have hrho0_measurable : MeasurableSet (rho 0) := (hrho 0).2
  have hrho1_subset : rho 1 ⊆ acceptAllPolicy := (hrho 1).1
  have hrho1_measurable : MeasurableSet (rho 1) := (hrho 1).2
  have hq_candidate :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        candidate (mu 0) :=
    hq0.mono_set hcandidate_subset
  have hq_current :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (rho 0) (mu 0) :=
    hq0.mono_set hrho0_subset
  have hw_candidate : IntegrableOn (w 0) candidate (mu 0) :=
    hw0.mono_set hcandidate_subset
  have hw_current : IntegrableOn (w 0) (rho 0) (mu 0) :=
    hw0.mono_set hrho0_subset
  have htime_candidate : IntegrableOn (fun tau : TripLength => tau) candidate (mu 0) :=
    htime0.mono_set hcandidate_subset
  have htime_current : IntegrableOn (fun tau : TripLength => tau) (rho 0) (mu 0) :=
    htime0.mono_set hrho0_subset
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
  have hT0'_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) candidate :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) candidate
      (le_of_lt harrival0_pos) hcandidate_measurable hcandidate_subset
  have hQ0'_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
      switch21 candidate (le_of_lt harrival0_pos) hswitch12_pos hsum0
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
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) candidate :=
    add_pos (mul_pos hQ0'_pos hT1_pos) (mul_pos hQ1_pos hT0'_pos)
  have hscore_candidate :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) candidate hq_candidate hw_candidate
      htime_candidate
  have hscore_current :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) (rho 0) hq_current hw_current
      htime_current
  have hlinear :
      gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 0) <=
        gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate := by
    rw [hscore_current, hscore_candidate]
    nlinarith
  have hcurrent_zero :
      gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 0) = 0 := by
    unfold gn21MeasuredLeftLinearScoreAtCurrent
    exact gn21AggregateDynamicReward_current_left_linear_score_eq_zero
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) hden_pos
  have hscore_nonneg :
      0 <=
        gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate := by
    linarith
  have hquot :=
    gn21AggregateDynamicReward_current_le_left_candidate_of_linearScore_nonneg
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1))
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate)
      (gn21ScaledStateTime (mu 0) (arrival 0) candidate)
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) candidate)
      hden'_pos (by
        simpa [gn21MeasuredLeftLinearScoreAtCurrent, mul_comm, mul_left_comm,
          mul_assoc] using hscore_nonneg)
  simpa [gn21AggregateDynamicRewardFunctional,
    gn21MeasuredAggregateRewardPrimitives, Function.update] using hquot

/-- Improving the actual right fixed-current marginal integral weakly improves
the actual Appendix-D aggregate reward. -/
theorem gn21AggregateDynamicRewardFunctional_le_update_right_of_marginal_le
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
    (hmarginal :
      lemma5MarginalSetReward (mu 1)
          (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1))
          (rho 1) <=
        lemma5MarginalSetReward (mu 1)
          (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1))
          candidate) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 1 candidate) := by
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
  have hlinear :
      gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 1) <=
        gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate := by
    rw [hscore_current, hscore_candidate]
    nlinarith
  have hcurrent_zero :
      gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 1) = 0 := by
    unfold gn21MeasuredRightLinearScoreAtCurrent
    exact gn21AggregateDynamicReward_current_right_linear_score_eq_zero
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) hden_pos
  have hscore_nonneg :
      0 <=
        gn21MeasuredRightLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate := by
    linarith
  have hquot :=
    gn21AggregateDynamicReward_current_le_right_candidate_of_linearScore_nonneg
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 candidate)
      (gn21ScaledStateTime (mu 1) (arrival 1) candidate)
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) candidate)
      hden'_pos (by
        simpa [gn21MeasuredRightLinearScoreAtCurrent, mul_comm, mul_left_comm,
          mul_assoc] using hscore_nonneg)
  simpa [gn21AggregateDynamicRewardFunctional,
    gn21MeasuredAggregateRewardPrimitives, Function.update] using hquot

/-- If a left-coordinate update cannot improve the actual Appendix-D aggregate
reward, its fixed-current marginal set reward cannot exceed the current set
reward. -/
theorem gn21MeasuredLeftMarginalSetReward_candidate_le_of_aggregate_update_le
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicFeasibleMeasurablePolicy rho)
    (candidate : TripPolicy)
    (hcandidate_subset : candidate ⊆ acceptAllPolicy)
    (hcandidate_measurable : MeasurableSet candidate)
    (hupdate :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0 candidate) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho) :
    lemma5MarginalSetReward (mu 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        candidate <=
      lemma5MarginalSetReward (mu 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (rho 0) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hrho0_subset : rho 0 ⊆ acceptAllPolicy := (hrho 0).1
  have hrho0_measurable : MeasurableSet (rho 0) := (hrho 0).2
  have hrho1_subset : rho 1 ⊆ acceptAllPolicy := (hrho 1).1
  have hrho1_measurable : MeasurableSet (rho 1) := (hrho 1).2
  have hq_candidate :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        candidate (mu 0) :=
    hq0.mono_set hcandidate_subset
  have hq_current :
      IntegrableOn (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (rho 0) (mu 0) :=
    hq0.mono_set hrho0_subset
  have hw_candidate : IntegrableOn (w 0) candidate (mu 0) :=
    hw0.mono_set hcandidate_subset
  have hw_current : IntegrableOn (w 0) (rho 0) (mu 0) :=
    hw0.mono_set hrho0_subset
  have htime_candidate : IntegrableOn (fun tau : TripLength => tau) candidate (mu 0) :=
    htime0.mono_set hcandidate_subset
  have htime_current : IntegrableOn (fun tau : TripLength => tau) (rho 0) (mu 0) :=
    htime0.mono_set hrho0_subset
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
  have hT0'_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) candidate :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) candidate
      (le_of_lt harrival0_pos) hcandidate_measurable hcandidate_subset
  have hQ0'_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12
      switch21 candidate (le_of_lt harrival0_pos) hswitch12_pos hsum0
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
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) candidate :=
    add_pos (mul_pos hQ0'_pos hT1_pos) (mul_pos hQ1_pos hT0'_pos)
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate)
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
          (gn21ScaledStateTime (mu 0) (arrival 0) candidate)
          (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) candidate)
          (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) <=
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
    gn21AggregateDynamicReward_candidate_left_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
      (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
      (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1))
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 candidate)
      (gn21ScaledStateTime (mu 0) (arrival 0) candidate)
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) candidate)
      hden_pos hden'_pos hquot
  have hlinear :
      gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) candidate <=
        gn21MeasuredLeftLinearScoreAtCurrent (mu 0) (mu 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (rho 0) (rho 1) (rho 0) := by
    simpa [gn21MeasuredLeftLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) candidate hq_candidate hw_candidate
      htime_candidate
  have hscore_current :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) (rho 0) hq_current hw_current
      htime_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith

/-- State-swapped aggregate-to-marginal bridge for a right-coordinate update. -/
theorem gn21MeasuredRightMarginalSetReward_candidate_le_of_aggregate_update_le
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
At an actual source-open optimum, deleting the surge-state policy to the open
empty policy cannot improve reward.  Transporting that comparison through the
actual aggregate quotient gives exactly the empty-policy fixed-marginal
inequality needed to rule out an all-negative increasing response at a
positive-mass optimum.
-/
theorem gn21MeasuredRightMarginalSetReward_empty_le_of_dynamicOpenOptimal
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
    exact dynamicFeasibleOpenPolicy_update hrho.1 1 ∅ (by simp) isOpen_empty
  have hempty_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1 ∅) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho :=
    hrho.2 _ hempty_open
  exact gn21MeasuredRightMarginalSetReward_candidate_le_of_aggregate_update_le
    mu arrival switch12 switch21 w harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hq1 hw1 htime1 hrho.1.to_measurable
    ∅ (by simp) MeasurableSet.empty hempty_reward

/-- Replacing the left policy by the positive set of its actual fixed-current
marginal response weakly improves the Appendix-D aggregate reward. -/
theorem gn21AggregateDynamicRewardFunctional_le_update_left_positiveResponse
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicFeasibleMeasurablePolicy rho) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 0
          (lemma5PositiveResponsePolicy
            (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 0) (w 1) (rho 0) (rho 1)))) := by
  let response :=
    gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1)
  let candidate := lemma5PositiveResponsePolicy response
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredLeftMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) hw0_measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 0) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) acceptAllPolicy hq0 hw0 htime0
  have hcandidate_subset : candidate ⊆ acceptAllPolicy := by
    dsimp [candidate]
    exact lemma5PositiveResponsePolicy_subset_acceptAll response
  have hcandidate_measurable : MeasurableSet candidate := by
    dsimp [candidate]
    exact measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable
  have hmarginal :
      lemma5MarginalSetReward (mu 0) response (rho 0) <=
        lemma5MarginalSetReward (mu 0) response candidate :=
    lemma5MarginalSetReward_le_positiveResponsePolicy
      (mu 0) response (rho 0) hresponse_measurable hresponse_integrable
      (hrho 0).2 (hrho 0).1
  simpa [response, candidate] using
    (gn21AggregateDynamicRewardFunctional_le_update_left_of_marginal_le
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hq0 hw0 htime0 hrho candidate
      hcandidate_subset hcandidate_measurable (by simpa [response] using hmarginal))

/-- Replacing the right policy by the positive set of its actual fixed-current
marginal response weakly improves the Appendix-D aggregate reward. -/
theorem gn21AggregateDynamicRewardFunctional_le_update_right_positiveResponse
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw1_measurable : Measurable (w 1))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicFeasibleMeasurablePolicy rho) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 1
          (lemma5PositiveResponsePolicy
            (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 0) (w 1) (rho 0) (rho 1)))) := by
  let response :=
    gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1)
  let candidate := lemma5PositiveResponsePolicy response
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredRightMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) hw1_measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 1) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) acceptAllPolicy hq1 hw1 htime1
  have hcandidate_subset : candidate ⊆ acceptAllPolicy := by
    dsimp [candidate]
    exact lemma5PositiveResponsePolicy_subset_acceptAll response
  have hcandidate_measurable : MeasurableSet candidate := by
    dsimp [candidate]
    exact measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable
  have hmarginal :
      lemma5MarginalSetReward (mu 1) response (rho 1) <=
        lemma5MarginalSetReward (mu 1) response candidate :=
    lemma5MarginalSetReward_le_positiveResponsePolicy
      (mu 1) response (rho 1) hresponse_measurable hresponse_integrable
      (hrho 1).2 (hrho 1).1
  simpa [response, candidate] using
    (gn21AggregateDynamicRewardFunctional_le_update_right_of_marginal_le
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hq1 hw1 htime1 hrho candidate
      hcandidate_subset hcandidate_measurable (by simpa [response] using hmarginal))

/--
An open-domain aggregate optimum has the non-surge source form almost
everywhere whenever its actual positive marginal-response policy has that
source form and a null zero boundary.  No measurable-domain extension or
endpoint-path derivative premise is used: the positive-response candidate is
itself source-open, so open optimality supplies the required comparison.
-/
theorem gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (shape : Lemma5DerivativeShape)
    (hpositive_response_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (rho 0) (rho 1))))
    (hpositive_zero_set_null :
      (mu 0)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
              (rho 0) (rho 1) tau = 0} = 0) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 0) shape (rho 0) := by
  let response :=
    gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (rho 0) (rho 1)
  let candidate := lemma5PositiveResponsePolicy response
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredLeftMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) hw0_measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 0) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) acceptAllPolicy hq0 hw0 htime0
  have hcandidate_form : lemma5SourcePolicyForm shape candidate := by
    simpa [candidate, response] using hpositive_response_form
  have hcandidate_subset : candidate ⊆ acceptAllPolicy :=
    lemma5SourcePolicyForm_subset_acceptAll hcandidate_form
  have hcandidate_open : IsOpen candidate :=
    lemma5SourcePolicyForm_open hcandidate_form
  have hcandidate_measurable : MeasurableSet candidate :=
    hcandidate_open.measurableSet
  have hupdate_open :
      dynamicFeasibleOpenPolicy (Function.update rho 0 candidate) :=
    dynamicFeasibleOpenPolicy_update hrho.1 0 candidate
      hcandidate_subset hcandidate_open
  have hupdate_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0 candidate) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho :=
    hrho.2 _ hupdate_open
  have hmarginal :
      lemma5MarginalSetReward (mu 0) response candidate <=
        lemma5MarginalSetReward (mu 0) response (rho 0) := by
    dsimp [response]
    exact gn21MeasuredLeftMarginalSetReward_candidate_le_of_aggregate_update_le
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hq0 hw0 htime0 hrho.1.to_measurable
      candidate hcandidate_subset hcandidate_measurable hupdate_reward
  exact lemma5SourcePolicyFormAlmostEverywhere_of_positiveResponse_candidate_le
    (mu 0) response shape (rho 0) hresponse_measurable hresponse_integrable
    (hrho.1 0).2.measurableSet (hrho.1 0).1 hcandidate_form
    (by simpa [response] using hpositive_zero_set_null) hmarginal

/-- State-swapped open-domain source-form classification for the surge policy. -/
theorem gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hw1_measurable : Measurable (w 1))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (shape : Lemma5DerivativeShape)
    (hpositive_response_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (rho 0) (rho 1))))
    (hpositive_zero_set_null :
      (mu 1)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
              (rho 0) (rho 1) tau = 0} = 0) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 1) shape (rho 1) := by
  let response :=
    gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (rho 0) (rho 1)
  let candidate := lemma5PositiveResponsePolicy response
  have hresponse_measurable : Measurable response := by
    dsimp [response]
    exact measurable_gn21MeasuredRightMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) hw1_measurable
  have hresponse_integrable : IntegrableOn response acceptAllPolicy (mu 1) := by
    dsimp [response]
    exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) acceptAllPolicy hq1 hw1 htime1
  have hcandidate_form : lemma5SourcePolicyForm shape candidate := by
    simpa [candidate, response] using hpositive_response_form
  have hcandidate_subset : candidate ⊆ acceptAllPolicy :=
    lemma5SourcePolicyForm_subset_acceptAll hcandidate_form
  have hcandidate_open : IsOpen candidate :=
    lemma5SourcePolicyForm_open hcandidate_form
  have hcandidate_measurable : MeasurableSet candidate :=
    hcandidate_open.measurableSet
  have hupdate_open :
      dynamicFeasibleOpenPolicy (Function.update rho 1 candidate) :=
    dynamicFeasibleOpenPolicy_update hrho.1 1 candidate
      hcandidate_subset hcandidate_open
  have hupdate_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1 candidate) <=
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho :=
    hrho.2 _ hupdate_open
  have hmarginal :
      lemma5MarginalSetReward (mu 1) response candidate <=
        lemma5MarginalSetReward (mu 1) response (rho 1) := by
    dsimp [response]
    exact gn21MeasuredRightMarginalSetReward_candidate_le_of_aggregate_update_le
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hq1 hw1 htime1 hrho.1.to_measurable
      candidate hcandidate_subset hcandidate_measurable hupdate_reward
  exact lemma5SourcePolicyFormAlmostEverywhere_of_positiveResponse_candidate_le
    (mu 1) response shape (rho 1) hresponse_measurable hresponse_integrable
    (hrho.1 1).2.measurableSet (hrho.1 1).1 hcandidate_form
    (by simpa [response] using hpositive_zero_set_null) hmarginal

/--
The actual aggregate replacement route for Theorem 4.

For every source-open policy, first restore the source's strict state-rate
order when needed using its surge-state witness.  Replace the non-surge
component by the positive set of its actual marginal response, recheck the
rate order, and then do the analogous surge replacement.  The two response
form assumptions are the remaining affine/source calculus obligations: they
are stated directly for the actual responses and are not packed into an
endpoint-variation or optimizer record.

This is deliberately a weak-dominance theorem.  Weak canonical dominance plus
compact continuity gives optimizer existence; the fixed-marginal route proves
the a.e. form of every optimizer separately.
-/
theorem gn21_exists_open_sourceForm_dominating_policy_of_actual_positiveResponses
    (mu : Fin 2 -> Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hleft_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 0)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1))))
    (hright_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 1)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1))))
    (rho : Fin 2 -> TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho) :
    exists tau : Fin 2 -> TripPolicy,
      dynamicFeasibleOpenPolicy tau /\
        lemma5SourcePolicyForm (shape 0) (tau 0) /\
          lemma5SourcePolicyForm (shape 1) (tau 1) /\
            gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
              gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w tau := by
  let R : DynamicReward :=
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
  let rate0 : (Fin 2 -> TripPolicy) -> Real := fun sigma =>
    gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (sigma 0)
  let rate1 : (Fin 2 -> TripPolicy) -> Real := fun sigma =>
    gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (sigma 1)
  have ensure_rate :
      forall sigma : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy sigma ->
          exists sigma' : Fin 2 -> TripPolicy,
            dynamicFeasibleOpenPolicy sigma' /\
              R sigma <= R sigma' /\
                rate0 sigma' < rate1 sigma' /\
                  sigma' 0 = sigma 0 := by
    intro sigma hsigma
    by_cases hrate_le : rate1 sigma <= rate0 sigma
    · rcases gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hsurge hsigma
          (by simpa [rate0, rate1] using hrate_le) with
        ⟨sigma2, hsigma2_subset, hsigma2_open, hdominates, himproves⟩
      let sigma' : Fin 2 -> TripPolicy := Function.update sigma 1 sigma2
      have hsigma'_open : dynamicFeasibleOpenPolicy sigma' := by
        dsimp [sigma']
        exact dynamicFeasibleOpenPolicy_update hsigma 1 sigma2 hsigma2_subset hsigma2_open
      have himproves_R : R sigma < R sigma' := by
        simpa [R, sigma'] using himproves
      have hrate_lt : rate0 sigma' < rate1 sigma' := by
        have h := hdominates (sigma' 0) (hsigma'_open 0).1 (hsigma'_open 0).2
        simpa [rate0, rate1, sigma'] using h
      refine ⟨sigma', hsigma'_open, le_of_lt himproves_R, hrate_lt, ?_⟩
      simp [sigma']
    · refine ⟨sigma, hsigma, le_rfl, lt_of_not_ge hrate_le, rfl⟩
  rcases ensure_rate rho hrho with
    ⟨rhoA, hrhoA_open, hrho_le_A, hrateA, hrhoA_zero⟩
  let leftCandidate : TripPolicy :=
    lemma5PositiveResponsePolicy
      (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
        (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rhoA 0) (rhoA 1))
  have hleft_formA : lemma5SourcePolicyForm (shape 0) leftCandidate := by
    dsimp [leftCandidate]
    exact hleft_source_form rhoA hrhoA_open (by simpa [rate0, rate1] using hrateA)
  have hleft_subset : leftCandidate ⊆ acceptAllPolicy :=
    lemma5SourcePolicyForm_subset_acceptAll hleft_formA
  have hleft_open : IsOpen leftCandidate :=
    lemma5SourcePolicyForm_open hleft_formA
  let rhoB : Fin 2 -> TripPolicy := Function.update rhoA 0 leftCandidate
  have hrhoB_open : dynamicFeasibleOpenPolicy rhoB := by
    dsimp [rhoB]
    exact dynamicFeasibleOpenPolicy_update hrhoA_open 0 leftCandidate
      hleft_subset hleft_open
  have hA_le_B : R rhoA <= R rhoB := by
    dsimp [R, rhoB, leftCandidate]
    exact gn21AggregateDynamicRewardFunctional_le_update_left_positiveResponse
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0
      hrhoA_open.to_measurable
  have hleft_formB : lemma5SourcePolicyForm (shape 0) (rhoB 0) := by
    simpa [rhoB] using hleft_formA
  rcases ensure_rate rhoB hrhoB_open with
    ⟨rhoC, hrhoC_open, hB_le_C, hrateC, hrhoC_zero⟩
  have hleft_formC : lemma5SourcePolicyForm (shape 0) (rhoC 0) := by
    rw [hrhoC_zero]
    exact hleft_formB
  let rightCandidate : TripPolicy :=
    lemma5PositiveResponsePolicy
      (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
        (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rhoC 0) (rhoC 1))
  have hright_formC : lemma5SourcePolicyForm (shape 1) rightCandidate := by
    dsimp [rightCandidate]
    exact hright_source_form rhoC hrhoC_open (by simpa [rate0, rate1] using hrateC)
  have hright_subset : rightCandidate ⊆ acceptAllPolicy :=
    lemma5SourcePolicyForm_subset_acceptAll hright_formC
  have hright_open : IsOpen rightCandidate :=
    lemma5SourcePolicyForm_open hright_formC
  let tau : Fin 2 -> TripPolicy := Function.update rhoC 1 rightCandidate
  have htau_open : dynamicFeasibleOpenPolicy tau := by
    dsimp [tau]
    exact dynamicFeasibleOpenPolicy_update hrhoC_open 1 rightCandidate
      hright_subset hright_open
  have hC_le_tau : R rhoC <= R tau := by
    dsimp [R, tau, rightCandidate]
    exact gn21AggregateDynamicRewardFunctional_le_update_right_positiveResponse
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1
      hrhoC_open.to_measurable
  refine ⟨tau, htau_open, ?_, ?_, ?_⟩
  · simpa [tau] using hleft_formC
  · simpa [tau] using hright_formC
  · exact hrho_le_A.trans (hA_le_B.trans (hB_le_C.trans hC_le_tau))

/--
Compact attainment from weak dominance by the *closed canonical endpoint
family*.  This intentionally differs from
`exists_dynamicOpenOptimal_of_weak_canonical_dominance`: it does not require
the canonical increasing endpoint to be finite.

That distinction is necessary for the surge affine-minus branch.  At an
arbitrary policy its positive fixed-marginal response may be empty, represented
by the compactified increasing cutoff at infinity.  Finiteness is recovered
only later, from fixed-marginal optimality at an attained optimum.
-/
theorem exists_dynamicOpenOptimal_of_weak_canonical_domain_dominance
    (R : DynamicReward)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hreplace :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          exists endpoints : GN21Lemma5CanonicalPairEndpointVector shape,
            endpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape /\
              R rho <= R (gn21Lemma5CanonicalPairPolicy shape endpoints)) :
    exists rho : Fin 2 -> TripPolicy, dynamicOpenOptimal R rho := by
  rcases
      (isCompact_gn21Lemma5CanonicalPairEndpointDomain shape).exists_isMaxOn
        (gn21Lemma5CanonicalPairEndpointDomain_nonempty shape)
        hpair_continuous with
    ⟨endpoints, hendpoints_domain, hendpoints_max⟩
  rw [isMaxOn_iff] at hendpoints_max
  let rhoStar := gn21Lemma5CanonicalPairPolicy shape endpoints
  have hrhoStar_feasible : dynamicFeasibleOpenPolicy rhoStar :=
    gn21Lemma5CanonicalPairPolicy_feasibleOpen shape endpoints
  refine ⟨rhoStar, hrhoStar_feasible, ?_⟩
  intro rho hrho
  rcases hreplace rho hrho with ⟨candidate, hcandidate_domain, hrho_le_candidate⟩
  exact hrho_le_candidate.trans (by
    simpa [rhoStar] using hendpoints_max candidate hcandidate_domain)

/-- The compactified increasing canonical family additionally represents the
empty policy at its infinity lower endpoint. -/
theorem exists_canonicalEndpointVector_of_increasing_sourceForm_or_empty
    (policy : TripPolicy)
    (hform_or_empty :
      lemma5SourcePolicyForm .strictlyIncreasing policy \/ policy = ∅) :
    ∃ endpoints ∈ gn21Lemma5CanonicalEndpointDomain .strictlyIncreasing,
      gn21EndpointVectorPolicy endpoints = policy := by
  rcases hform_or_empty with hform | hempty
  · exact exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform
  · subst policy
    let endpoints : GN21Lemma5EndpointVector 0 :=
      ![(⊤ : ℝ≥0∞), (⊤ : ℝ≥0∞)]
    have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [endpoints]
    refine ⟨endpoints, ?_, ?_⟩
    · change endpoints ∈ gn21Lemma5EndpointDomain .strictlyIncreasing 0
      refine ⟨hordered, ?_⟩
      change endpoints 1 = ∞
      simp [endpoints]
    · change gn21EndpointVectorPolicy (n := 1) endpoints = ∅
      rw [gn21EndpointVectorPolicy_one]
      simp [endpoints]

/--
Convert a source positive-response form to the compact canonical endpoint
domain.  The only non-source-form alternative is the empty policy in the
increasing branch, whose infinity endpoint is part of that compact domain.

This is an existence-device only.  It deliberately does not identify the
empty policy with the paper's finite increasing-tail conclusion.
-/
theorem exists_canonicalEndpointVector_of_sourceForm_or_increasing_empty
    (shape : Lemma5DerivativeShape)
    (policy : TripPolicy)
    (hform_or_empty :
      lemma5SourcePolicyForm shape policy \/
        (shape = .strictlyIncreasing /\ policy = ∅)) :
    ∃ endpoints ∈ gn21Lemma5CanonicalEndpointDomain shape,
      gn21EndpointVectorPolicy endpoints = policy := by
  rcases hform_or_empty with hform | ⟨hshape, hempty⟩
  · exact exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform
  · subst shape
    exact exists_canonicalEndpointVector_of_increasing_sourceForm_or_empty
      policy (Or.inr hempty)

/-- A pointwise positive actual marginal response selects accept-all exactly,
with an empty zero boundary.  This early version is used by the direct affine
canonical assembly below. -/
theorem lemma5SourcePolicyForm_and_zeroSetNull_of_pointwise_positive_direct
    (mu : Measure TripLength)
    (response : TripLength -> Real)
    (hpositive : forall tau : TripLength, 0 < tau -> 0 < response tau) :
    lemma5SourcePolicyForm .positive
        (lemma5PositiveResponsePolicy response) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  have hpolicy : lemma5PositiveResponsePolicy response = acceptAllPolicy := by
    ext tau
    constructor
    · intro htau
      exact htau.1
    · intro htau
      exact ⟨htau, hpositive tau htau⟩
  constructor
  · exact hpolicy
  · have hzero_empty : {tau : TripLength | 0 < tau /\ response tau = 0} = ∅ := by
      ext tau
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨htau, hzero⟩
      exact (ne_of_gt (hpositive tau htau)) hzero
    rw [hzero_empty, measure_empty]

/--
The non-surge half of the Theorem 4 source price table gives a compact
canonical representative of the actual Appendix-D positive marginal response
at every rate-ordered feasible policy.  All quotient, scale, and rate facts
are derived below from the policy and source primitives rather than supplied
through a conclusion-bearing certificate.
-/
theorem gn21_left_sourceForm_and_zeroSetNull_of_affine_source_case
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive)) :
    forall rho : Fin 2 -> TripPolicy,
      dynamicFeasibleOpenPolicy rho ->
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
          gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 0)
              (lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1))) /\
            (mu 0)
              {tau : TripLength |
                0 < tau /\
                  gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1) tau = 0} = 0 := by
  intro rho hrho hrate
  have hrho_meas : dynamicFeasibleMeasurablePolicy rho := hrho.to_measurable
  have hsum0 : 0 < switch12 + switch21 :=
    add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 :=
    add_pos hswitch21_pos hswitch12_pos
  have hT0_pos :
      0 < gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (rho 0)
      (le_of_lt harrival0_pos) (hrho_meas 0).2 (hrho_meas 0).1
  have hT1_pos :
      0 < gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (rho 1)
      (le_of_lt harrival1_pos) (hrho_meas 1).2 (hrho_meas 1).1
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
        (rho 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
      switch12 switch21 (rho 0) (le_of_lt harrival0_pos) hswitch12_pos
      hsum0 (hrho_meas 0).2 (hrho_meas 0).1
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
        (rho 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
      switch21 switch12 (rho 1) (le_of_lt harrival1_pos) hswitch21_pos
      hsum1 (hrho_meas 1).2 (hrho_meas 1).1
  have hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) /
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) /
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    add_pos (div_pos hQ0_pos hT0_pos) (div_pos hQ1_pos hT1_pos)
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0)
  let Rj := gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1)
  have hRi_lt_Rj : Ri < Rj := by
    simpa [Ri, Rj] using hrate
  have hW0 :
      gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0) =
        Ri * gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 0) (arrival 0) Ri (w 0) (rho 0) harrival0_pos
      (hrho_meas 0).2 (hrho_meas 0).1 rfl
  have hW1 :
      gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1) =
        Rj * gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 1) (arrival 1) Rj (w 1) (rho 1) harrival1_pos
      (hrho_meas 1).2 (hrho_meas 1).1 rfl
  rcases hnonsurge_price_case with
      ⟨m, a, ha_nonneg, hprice, hshape⟩ |
        ⟨m, a, ha_pos, hprice, hshape⟩ | ⟨hpositive, hshape⟩
  · rcases gn21MeasuredLeft_positiveAffineMarginal_sourceLeftForm_and_zeroSetNull
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        m a Ri Rj (w 1) (rho 0) (rho 1) hRi_lt_Rj ha_nonneg
        hstate_weight_pos hswitch12_pos hsum0 hQ1_pos hT0_pos hT1_pos
        hden_pos (by simpa [hprice] using hW0) hW1 with ⟨hform, hzero⟩
    constructor
    · rw [hprice, hshape]
      exact hform
    · rw [hprice]
      exact hzero
  · rcases gn21MeasuredLeft_negativeAffineMarginal_sourceMiddleForm_and_zeroSetNull
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        m (-a) Ri Rj (w 1) (rho 0) (rho 1) hstate_weight_pos
        (neg_lt_zero.mpr ha_pos) (by linarith) hswitch12_pos hsum0 hQ1_pos
        hT0_pos hT1_pos hden_pos (by simpa [hprice] using hW0) hW1 with
      ⟨hform, hzero⟩
    constructor
    · rw [hprice, hshape]
      exact hform
    · rw [hprice]
      exact hzero
  · rcases lemma5SourcePolicyForm_and_zeroSetNull_of_pointwise_positive_direct
        (mu 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (hpositive rho hrho) with ⟨hform, hzero⟩
    constructor
    · rw [hshape]
      exact hform
    · exact hzero

/-- The compact endpoint corollary of the direct non-surge affine response
classification. -/
theorem gn21_exists_leftCanonicalEndpoint_of_affine_source_case
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive)) :
    forall rho : Fin 2 -> TripPolicy,
      dynamicFeasibleOpenPolicy rho ->
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
          gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 0) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1)) := by
  intro rho hrho hrate
  rcases gn21_left_sourceForm_and_zeroSetNull_of_affine_source_case
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hnonsurge_price_case rho hrho hrate with
    ⟨hform, _⟩
  exact exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform

/--
The surge half of the Theorem 4 source price table gives a compact canonical
representative of the actual Appendix-D positive marginal response at every
rate-ordered feasible policy.  The affine-minus branch is deliberately
allowed to use the compactified empty increasing endpoint; this theorem makes
no finite-tail assertion.
-/
theorem gn21_right_sourceForm_or_empty_and_zeroSetNull_of_affine_source_case
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive)) :
    forall rho : Fin 2 -> TripPolicy,
      dynamicFeasibleOpenPolicy rho ->
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
          gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          (lemma5SourcePolicyForm (shape 1)
              (lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1))) \/
            (shape 1 = .strictlyIncreasing /\
              lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1)) = ∅)) /\
            (mu 1)
              {tau : TripLength |
                0 < tau /\
                  gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1) tau = 0} = 0 := by
  intro rho hrho hrate
  have hrho_meas : dynamicFeasibleMeasurablePolicy rho := hrho.to_measurable
  have hsum0 : 0 < switch12 + switch21 :=
    add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 :=
    add_pos hswitch21_pos hswitch12_pos
  have hT0_pos :
      0 < gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (rho 0)
      (le_of_lt harrival0_pos) (hrho_meas 0).2 (hrho_meas 0).1
  have hT1_pos :
      0 < gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (rho 1)
      (le_of_lt harrival1_pos) (hrho_meas 1).2 (hrho_meas 1).1
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
        (rho 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0)
      switch12 switch21 (rho 0) (le_of_lt harrival0_pos) hswitch12_pos
      hsum0 (hrho_meas 0).2 (hrho_meas 0).1
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
        (rho 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1)
      switch21 switch12 (rho 1) (le_of_lt harrival1_pos) hswitch21_pos
      hsum1 (hrho_meas 1).2 (hrho_meas 1).1
  have hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) /
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) /
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (div_pos hQ1_pos hT1_pos) (div_pos hQ0_pos hT0_pos)
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0)
  let Rj := gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1)
  have hRi_lt_Rj : Ri < Rj := by
    simpa [Ri, Rj] using hrate
  have hW0 :
      gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0) =
        Ri * gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 0) (arrival 0) Ri (w 0) (rho 0) harrival0_pos
      (hrho_meas 0).2 (hrho_meas 0).1 rfl
  have hW1 :
      gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1) =
        Rj * gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 1) (arrival 1) Rj (w 1) (rho 1) harrival1_pos
      (hrho_meas 1).2 (hrho_meas 1).1 rfl
  rcases hsurge_price_case with
      ⟨m, a, ha_nonneg, hprice, hshape⟩ |
        ⟨m, a, ha_pos, hprice, hshape⟩ | ⟨hpositive, hshape⟩
  · rcases gn21MeasuredRight_negativeAffineMarginal_sourceForm_or_empty_and_zeroSetNull
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        m a Ri Rj (w 0) (rho 0) (rho 1) hRi_lt_Rj ha_nonneg
        hstate_weight_pos hswitch21_pos hsum1 hQ0_pos hT0_pos hT1_pos
        hden_pos hW0 (by simpa [hprice] using hW1) with ⟨hform_or_empty, hzero⟩
    constructor
    · rw [hprice, hshape]
      rcases hform_or_empty with hform | hempty
      · exact Or.inl hform
      · exact Or.inr ⟨rfl, hempty⟩
    · rw [hprice]
      exact hzero
  · rcases gn21MeasuredRight_positiveAffineMarginal_sourceTwoTailForm_and_zeroSetNull
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        m a Ri Rj (w 0) (rho 0) (rho 1) hstate_weight_pos ha_pos
        (by linarith) hswitch21_pos hsum1 hQ0_pos hT0_pos hT1_pos hden_pos
        hW0 (by simpa [hprice] using hW1) with ⟨hform, hzero⟩
    constructor
    · rw [hprice, hshape]
      exact Or.inl hform
    · rw [hprice]
      exact hzero
  · rcases lemma5SourcePolicyForm_and_zeroSetNull_of_pointwise_positive_direct
        (mu 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (rho 0) (rho 1))
        (hpositive rho hrho) with ⟨hform, hzero⟩
    constructor
    · rw [hshape]
      exact Or.inl hform
    · exact hzero

/-- The compact endpoint corollary of the direct surge affine response
classification.  Only the increasing empty branch uses the compactification. -/
theorem gn21_exists_rightCanonicalEndpoint_of_affine_source_case
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive)) :
    forall rho : Fin 2 -> TripPolicy,
      dynamicFeasibleOpenPolicy rho ->
        gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
          gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 1) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1)) := by
  intro rho hrho hrate
  rcases gn21_right_sourceForm_or_empty_and_zeroSetNull_of_affine_source_case
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge_price_case rho hrho hrate with
    ⟨hform_or_empty, _⟩
  exact exists_canonicalEndpointVector_of_sourceForm_or_increasing_empty
    (shape 1)
    (lemma5PositiveResponsePolicy
      (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
        (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rho 0) (rho 1)))
    hform_or_empty

/-- A pointwise positive actual marginal response selects accept-all exactly,
with an empty zero boundary. -/
theorem lemma5SourcePolicyForm_and_zeroSetNull_of_pointwise_positive
    (mu : Measure TripLength)
    (response : TripLength -> Real)
    (hpositive : forall tau : TripLength, 0 < tau -> 0 < response tau) :
    lemma5SourcePolicyForm .positive
        (lemma5PositiveResponsePolicy response) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  have hpolicy : lemma5PositiveResponsePolicy response = acceptAllPolicy := by
    ext tau
    constructor
    · intro htau
      exact htau.1
    · intro htau
      exact ⟨htau, hpositive tau htau⟩
  constructor
  · exact hpolicy
  · have hzero_empty : {tau : TripLength | 0 < tau /\ response tau = 0} = ∅ := by
      ext tau
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨htau, hzero⟩
      exact (ne_of_gt (hpositive tau htau)) hzero
    rw [hzero_empty, measure_empty]

/--
Actual aggregate weak replacement into the compact canonical endpoint family.

Unlike the stronger exact-source-form version above, this target permits the
increasing branch's compactified empty policy.  It is therefore the correct
existence route for the source's affine surge-minus case; it does not weaken
the eventual theorem because the finite-tail conclusion is proved separately
at a genuine optimum.
-/
theorem gn21_exists_open_canonical_dominating_policy_of_actual_positiveResponses
    (mu : Fin 2 -> Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hleft_canonical :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 0) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1)))
    (hright_canonical :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 1) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1)))
    (rho : Fin 2 -> TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho) :
    exists endpoints : GN21Lemma5CanonicalPairEndpointVector shape,
      endpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape /\
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho <=
          gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
            (gn21Lemma5CanonicalPairPolicy shape endpoints) := by
  let R : DynamicReward :=
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
  let rate0 : (Fin 2 -> TripPolicy) -> Real := fun sigma =>
    gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (sigma 0)
  let rate1 : (Fin 2 -> TripPolicy) -> Real := fun sigma =>
    gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (sigma 1)
  have ensure_rate :
      forall sigma : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy sigma ->
          exists sigma' : Fin 2 -> TripPolicy,
            dynamicFeasibleOpenPolicy sigma' /\
              R sigma <= R sigma' /\
                rate0 sigma' < rate1 sigma' /\
                  sigma' 0 = sigma 0 := by
    intro sigma hsigma
    by_cases hrate_le : rate1 sigma <= rate0 sigma
    · rcases gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hsurge hsigma
          (by simpa [rate0, rate1] using hrate_le) with
        ⟨sigma2, hsigma2_subset, hsigma2_open, hdominates, himproves⟩
      let sigma' : Fin 2 -> TripPolicy := Function.update sigma 1 sigma2
      have hsigma'_open : dynamicFeasibleOpenPolicy sigma' := by
        dsimp [sigma']
        exact dynamicFeasibleOpenPolicy_update hsigma 1 sigma2 hsigma2_subset hsigma2_open
      have himproves_R : R sigma < R sigma' := by
        simpa [R, sigma'] using himproves
      have hrate_lt : rate0 sigma' < rate1 sigma' := by
        have h := hdominates (sigma' 0) (hsigma'_open 0).1 (hsigma'_open 0).2
        simpa [rate0, rate1, sigma'] using h
      refine ⟨sigma', hsigma'_open, le_of_lt himproves_R, hrate_lt, ?_⟩
      simp [sigma']
    · refine ⟨sigma, hsigma, le_rfl, lt_of_not_ge hrate_le, rfl⟩
  rcases ensure_rate rho hrho with
    ⟨rhoA, hrhoA_open, hrho_le_A, hrateA, _hrhoA_zero⟩
  rcases hleft_canonical rhoA hrhoA_open
      (by simpa [rate0, rate1] using hrateA) with
    ⟨leftEndpoints, hleft_domain, hleft_policy⟩
  let leftCandidate : TripPolicy := gn21EndpointVectorPolicy leftEndpoints
  have hleft_subset : leftCandidate ⊆ acceptAllPolicy := by
    dsimp [leftCandidate]
    exact gn21EndpointVectorPolicy_subset_acceptAll leftEndpoints
  have hleft_open : IsOpen leftCandidate := by
    dsimp [leftCandidate]
    exact gn21EndpointVectorPolicy_open leftEndpoints
  let rhoB : Fin 2 -> TripPolicy := Function.update rhoA 0 leftCandidate
  have hrhoB_open : dynamicFeasibleOpenPolicy rhoB := by
    dsimp [rhoB]
    exact dynamicFeasibleOpenPolicy_update hrhoA_open 0 leftCandidate
      hleft_subset hleft_open
  have hA_le_B : R rhoA <= R rhoB := by
    dsimp [R, rhoB, leftCandidate]
    rw [hleft_policy]
    exact gn21AggregateDynamicRewardFunctional_le_update_left_positiveResponse
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0
      hrhoA_open.to_measurable
  rcases ensure_rate rhoB hrhoB_open with
    ⟨rhoC, hrhoC_open, hB_le_C, hrateC, hrhoC_zero⟩
  have hleft_C : rhoC 0 = gn21EndpointVectorPolicy leftEndpoints := by
    rw [hrhoC_zero]
    rfl
  rcases hright_canonical rhoC hrhoC_open
      (by simpa [rate0, rate1] using hrateC) with
    ⟨rightEndpoints, hright_domain, hright_policy⟩
  let rightCandidate : TripPolicy := gn21EndpointVectorPolicy rightEndpoints
  have hright_subset : rightCandidate ⊆ acceptAllPolicy := by
    dsimp [rightCandidate]
    exact gn21EndpointVectorPolicy_subset_acceptAll rightEndpoints
  have hright_open : IsOpen rightCandidate := by
    dsimp [rightCandidate]
    exact gn21EndpointVectorPolicy_open rightEndpoints
  let tau : Fin 2 -> TripPolicy := Function.update rhoC 1 rightCandidate
  have htau_open : dynamicFeasibleOpenPolicy tau := by
    dsimp [tau]
    exact dynamicFeasibleOpenPolicy_update hrhoC_open 1 rightCandidate
      hright_subset hright_open
  have hC_le_tau : R rhoC <= R tau := by
    dsimp [R, tau, rightCandidate]
    rw [hright_policy]
    exact gn21AggregateDynamicRewardFunctional_le_update_right_positiveResponse
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1
      hrhoC_open.to_measurable
  let endpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
    (leftEndpoints, rightEndpoints)
  have hendpoints_domain : endpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
    ⟨hleft_domain, hright_domain⟩
  have hendpoints_policy :
      gn21Lemma5CanonicalPairPolicy shape endpoints = tau := by
    funext i
    fin_cases i
    · simpa [endpoints, gn21Lemma5CanonicalPairPolicy, tau] using hleft_C.symm
    · simp [endpoints, gn21Lemma5CanonicalPairPolicy, tau, rightCandidate]
  refine ⟨endpoints, hendpoints_domain, ?_⟩
  rw [hendpoints_policy]
  exact hrho_le_A.trans (hA_le_B.trans (hB_le_C.trans hC_le_tau))

/--
Actual Appendix-D optimizer existence from canonical positive-response
representations.  Continuity is discharged from the actual aggregate
functional, including every endpoint-complete middle/two-tail family; the
increasing compactification is allowed to select its empty endpoint here.
-/
theorem exists_gn21AggregateDynamicOpenOptimal_of_actual_canonical_positiveResponses
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hleft_canonical :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 0) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1)))
    (hright_canonical :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          exists endpoints :
              GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)),
            endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 1) /\
              gn21EndpointVectorPolicy endpoints =
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                    (arrival 0) (arrival 1) switch12 switch21
                    (w 0) (w 1) (rho 0) (rho 1))) :
    exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  exact exists_dynamicOpenOptimal_of_weak_canonical_domain_dominance
    (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
    shape
    (continuousOn_gn21AggregateDynamicRewardFunctional_canonicalPair
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos htime0 htime1 hw0 hw1)
    (fun rho hrho =>
      gn21_exists_open_canonical_dominating_policy_of_actual_positiveResponses
        mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable hq0 hq1
        hw0 hw1 htime0 htime1 hsurge hleft_canonical hright_canonical
        rho hrho)

/--
Direct source-price-table existence theorem for GN21 Theorem 4.  The proof
uses the actual Appendix-D aggregate functional, actual marginal responses,
and the compact endpoint family.  In the surge affine-minus case the compact
existence step may select the empty increasing endpoint; the printed finite
tail is a separate actual-optimum consequence and is not asserted here.
-/
theorem exists_gn21AggregateDynamicOpenOptimal_of_affine_source_price_cases
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive))
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive)) :
    exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho := by
  exact exists_gn21AggregateDynamicOpenOptimal_of_actual_canonical_positiveResponses
    mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
    hw0 hw1 hsurge
    (gn21_exists_leftCanonicalEndpoint_of_affine_source_case
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hnonsurge_price_case)
    (gn21_exists_rightCanonicalEndpoint_of_affine_source_case
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge_price_case)

/--
Every actual source-open optimum has the Theorem 4 policy forms up to the
paper's statewise null-set convention.  The affine-minus surge row is handled
by its dedicated actual-optimum theorem, which derives a finite tail instead
of treating the compact empty endpoint as a theorem conclusion.
-/
theorem gn21_affine_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive))
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive))
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
      lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  have hrate :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
        gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) :=
    gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  rcases gn21_left_sourceForm_and_zeroSetNull_of_affine_source_case
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hnonsurge_price_case rho hrho.1 hrate with
    ⟨hleft_form, hleft_zero⟩
  have hleft_ae :
      lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) :=
    gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
      mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0 (shape 0)
      hleft_form hleft_zero
  refine ⟨hleft_ae, ?_⟩
  rcases hsurge_price_case with
      ⟨m, a, ha_nonneg, hprice, hshape⟩ |
        ⟨m, a, ha_pos, hprice, hshape⟩ | ⟨hpositive, hshape⟩
  · rcases gn21MeasuredRight_negativeAffineMarginal_sourceFiniteForm_and_zeroSetNull_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w m a hprice harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos ha_nonneg hsurge hq1 hw1 htime1 hrho with
      ⟨hform, hzero⟩
    have hform_shape :
        lemma5SourcePolicyForm (shape 1)
          (lemma5PositiveResponsePolicy
            (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 0) (w 1) (rho 0) (rho 1))) := by
      rw [hshape]
      exact hform
    exact gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
      mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
      hform_shape hzero
  · rcases gn21_right_sourceForm_or_empty_and_zeroSetNull_of_affine_source_case
        mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos
        (Or.inr (Or.inl ⟨m, a, ha_pos, hprice, hshape⟩))
        rho hrho.1 hrate with ⟨hform_or_empty, hzero⟩
    rcases hform_or_empty with hform | ⟨hincreasing, _⟩
    · exact gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
        hform hzero
    · have hfalse : False := by
        simpa [hshape] using hincreasing
      exact hfalse.elim
  · rcases gn21_right_sourceForm_or_empty_and_zeroSetNull_of_affine_source_case
        mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos
        (Or.inr (Or.inr ⟨hpositive, hshape⟩))
        rho hrho.1 hrate with ⟨hform_or_empty, hzero⟩
    rcases hform_or_empty with hform | ⟨hincreasing, _⟩
    · exact gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
        hform hzero
    · have hfalse : False := by
        simpa [hshape] using hincreasing
      exact hfalse.elim

/--
An open optimum that has source-form representatives almost everywhere can be
replaced by exact source-form representatives without changing the Appendix-D
reward.  This is only the source's null-set convention, not a compactness or
endpoint-calculus premise.
-/
theorem exists_dynamicOpenOptimal_sourceForms_of_policyFormsAlmostEverywhere
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho)
    (hleft : lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0))
    (hright : lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1)) :
    exists rhoStar : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
          rhoStar /\
        lemma5SourcePolicyForm (shape 0) (rhoStar 0) /\
          lemma5SourcePolicyForm (shape 1) (rhoStar 1) := by
  rcases hleft with ⟨leftRepresentative, hleft_form, hleft_ae⟩
  rcases hright with ⟨rightRepresentative, hright_form, hright_ae⟩
  let rhoStar : Fin 2 -> TripPolicy :=
    Function.update (Function.update rho 0 leftRepresentative) 1 rightRepresentative
  have hrhoStar_feasible : dynamicFeasibleOpenPolicy rhoStar := by
    intro i
    fin_cases i
    · simpa [rhoStar] using
        And.intro (lemma5SourcePolicyForm_subset_acceptAll hleft_form)
          (lemma5SourcePolicyForm_open hleft_form)
    · simpa [rhoStar] using
        And.intro (lemma5SourcePolicyForm_subset_acceptAll hright_form)
          (lemma5SourcePolicyForm_open hright_form)
  have hleft_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0 leftRepresentative) :=
    gn21AggregateDynamicRewardFunctional_congr_left_policy_ae
      mu arrival switch12 switch21 w hleft_ae
  have hright_ae_after_left :
      policyAlmostEverywhereEq (mu 1)
        ((Function.update rho 0 leftRepresentative) 1) rightRepresentative := by
    simpa using hright_ae
  have hright_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0 leftRepresentative) =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rhoStar := by
    simpa [rhoStar] using
      (gn21AggregateDynamicRewardFunctional_congr_right_policy_ae
        mu arrival switch12 switch21 w hright_ae_after_left)
  have hrhoStar_reward :
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho =
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rhoStar :=
    hleft_reward.trans hright_reward
  have hrhoStar :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rhoStar := by
    refine ⟨hrhoStar_feasible, ?_⟩
    intro tau htau
    rw [← hrhoStar_reward]
    exact hrho.2 tau htau
  refine ⟨rhoStar, hrhoStar, ?_, ?_⟩
  · simpa [rhoStar] using hleft_form
  · simpa [rhoStar] using hright_form

/--
Source-facing direct Theorem 4 assembly.  It contains no legacy endpoint-sign
record: compact attainment is proved from the actual Appendix-D objective,
and every open optimum is classified from its actual fixed-current marginal
responses.  In particular, the finite surge affine-minus tail follows only
after open optimality is available.
-/
theorem paper_theorem4_affine_source_price_cases_direct
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 0 = affinePricing m a /\
          shape 0 = .strictlyDecreasing) \/
      (exists m a : Real,
        0 < a /\ w 0 = affinePricing m (-a) /\
          shape 0 = .strictlyQuasiConcave) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 0 = .positive))
    (hsurge_price_case :
      (exists m a : Real,
        0 <= a /\ w 1 = affinePricing m (-a) /\
          shape 1 = .strictlyIncreasing) \/
      (exists m a : Real,
        0 < a /\ w 1 = affinePricing m a /\
          shape 1 = .strictlyQuasiConvex) \/
      ((forall rho : Fin 2 -> TripPolicy,
          dynamicFeasibleOpenPolicy rho ->
            forall tau : TripLength, 0 < tau ->
              0 <
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau) /\
        shape 1 = .positive)) :
    (exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
          rho /\
        lemma5SourcePolicyForm (shape 0) (rho 0) /\
          lemma5SourcePolicyForm (shape 1) (rho 1)) /\
      forall rho : Fin 2 -> TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
            rho ->
          lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
            lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  rcases exists_gn21AggregateDynamicOpenOptimal_of_affine_source_price_cases
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
      hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case with ⟨rho, hrho⟩
  have hrho_forms :
      lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
        lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) :=
    gn21_affine_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
      hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hrho
  rcases exists_dynamicOpenOptimal_sourceForms_of_policyFormsAlmostEverywhere
      mu arrival switch12 switch21 w shape hrho hrho_forms.1 hrho_forms.2 with
    ⟨rhoStar, hrhoStar, hform0, hform1⟩
  refine ⟨⟨rhoStar, hrhoStar, hform0, hform1⟩, ?_⟩
  intro rho hrho
  exact gn21_affine_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
    mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
    hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hrho

/-!
## Source-form attainment and all-optimum classification

The following assembly theorems deliberately expose the three remaining
mathematical ingredients, each with its actual semantic target:

* continuity of the Appendix-D reward on the compact canonical family;
* source-form identification of the two *actual* fixed-current marginal
  positive policies when the source rate order holds; and
* nullity of their zero-response boundaries.

They are not a replacement record.  In particular, no arbitrary reward,
response, margin, endpoint derivative, or future-policy quantifier occurs in
the interface.  Concrete affine calculus theorems discharge these arguments.
-/

/-- Direct compact-attainment assembly for the actual Appendix-D objective.

The policy-by-policy replacement is the direct aggregate theorem above.  The
only analytic input here is continuity on the explicitly parameterized compact
canonical family. -/
theorem exists_gn21AggregateDynamicOpenOptimal_sourceForms_of_actual_positiveResponses
    (mu : Fin 2 -> Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
            (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hleft_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 0)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1))))
    (hright_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 1)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1)))) :
    exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
          rho /\
        lemma5SourcePolicyForm (shape 0) (rho 0) /\
          lemma5SourcePolicyForm (shape 1) (rho 1) := by
  exact
    exists_dynamicOpenOptimal_of_weak_canonical_dominance
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
      shape hpair_continuous
      (fun rho hrho =>
        gn21_exists_open_sourceForm_dominating_policy_of_actual_positiveResponses
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable hq0 hq1
          hw0 hw1 htime0 htime1 hsurge hleft_source_form hright_source_form
          rho hrho)

/-- Direct all-open-optima classification for the actual Appendix-D objective.

At an actual optimum the source surge-state dominance gives the rate order,
so the same concrete fixed-marginal source-form theorems apply.  The two
zero-boundary hypotheses are used solely to state equality modulo the source
measure, never to alter the objective. -/
theorem gn21Aggregate_openOptimal_sourceFormsAlmostEverywhere_of_actual_positiveResponses
    (mu : Fin 2 -> Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0))
    (hw1_measurable : Measurable (w 1))
    (hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0))
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hleft_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 0)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1))))
    (hright_source_form :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          lemma5SourcePolicyForm (shape 1)
            (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                (arrival 0) (arrival 1) switch12 switch21
                (w 0) (w 1) (rho 0) (rho 1))))
    (hleft_zero_set_null :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          (mu 0)
            {tau : TripLength |
              0 < tau /\
                gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau = 0} = 0)
    (hright_zero_set_null :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) ->
          (mu 1)
            {tau : TripLength |
              0 < tau /\
                gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
                  (arrival 0) (arrival 1) switch12 switch21
                  (w 0) (w 1) (rho 0) (rho 1) tau = 0} = 0)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w)
        rho) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) /\
      lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  have hrate :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
        gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) :=
    gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  refine ⟨?_, ?_⟩
  · exact
      gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0 (shape 0)
        (hleft_source_form rho hrho.1 hrate)
        (hleft_zero_set_null rho hrho.1 hrate)
  · exact
      gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
        (hright_source_form rho hrho.1 hrate)
        (hright_zero_set_null rho hrho.1 hrate)

end GN21DriverSurgePricing
