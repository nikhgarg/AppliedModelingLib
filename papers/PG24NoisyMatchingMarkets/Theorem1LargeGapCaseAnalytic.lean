import PG24NoisyMatchingMarkets.Theorem1AnalyticTailBridge
import PG24NoisyMatchingMarkets.Theorem3ChebyshevRates
import Mathlib.Tactic

/-!
# PG24 Theorem 1 large-gap analytic closure

The low cutoff block is controlled by the full iid maximum, while the middle
value mass is controlled by full-market affordance.  These are distinct
probabilities: the source's Case 2 proof cannot replace the latter with
upper-block affordance.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter MeasureTheory
open AppliedModelingLib.Matching

/--
An upper cutoff block is no easier to cross than the full iid coalition at
its common cutoff floor.  This is the Case 2 low-side maximum event, with no
partition-cardinality approximation.
-/
theorem theorem1_iid_atOrAbove_affordance_le_full_max_deviation
    {n : ℕ} [NeZero n] (noiseLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    (pivot value center deviation : ℝ)
    (hseparation : center + deviation ≤ pivot - value) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (theorem1CutoffAtOrAboveBlock active cutoff pivot) value cutoff ≤
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) center deviation := by
  let upper := theorem1CutoffAtOrAboveBlock active cutoff pivot
  calc
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) upper value cutoff ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) upper value
          (fun _ => pivot) :=
      AppliedModelingLib.Matching.cutoffCrossingProbability_le_constantCutoff_of_le
        (Measure.pi (fun _ : Fin n => noiseLaw)) (by
          intro college hcollege
          exact (Finset.mem_filter.mp hcollege).2)
    _ ≤ cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) value (fun _ => pivot) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin n => noiseLaw)) (Finset.subset_univ upper)
    _ ≤ AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) center deviation := by
      simpa [cutoffAffordanceProbability] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
          (Measure.pi (fun _ : Fin n => noiseLaw)) hseparation)

/--
The Case 2 full-coalition maximum deviation has the source `C^-K` rate.
Unlike the high-side one-college step, this follows directly from the
beta-max variance premise because the event is a maximum over all `C + 1`
noise draws.
-/
theorem theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ -> ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C)
            (Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem3_iidMaximum_powerDeviation_eventually_le_of_beta
    (blockExponent := (1 : ℝ))
    (deviationExponent := theorem1TailPhi4 beta gamma)
    noiseLaw hbeta hvariance (fun C : ℕ => C) tendsto_id (by
      filter_upwards with C
      calc
        Real.rpow (C : ℝ) (1 : ℝ) = (C : ℝ) := Real.rpow_one _
        _ ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ C)
    with ⟨A, hA_nonneg, hbound⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hbound] with C hC
  simpa [theorem1Tail_case2_chebyshev_exp_eq_neg_K beta gamma] using hC

/--
The corrected Case 2 integral estimate.  A low-side bound for the upper
cutoff block and a high-side bound for the full market imply a low-value
upper-block bound.  The high-side estimate is deliberately on the full
market, matching the capacity argument in the source proof.
-/
theorem theorem1_largeGap_upper_affordance_low_integral_le_of_primitives
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (upper : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    {lowPivot vS totalSupply lowError highError : ℝ}
    (hlow_error_nonneg : 0 ≤ lowError)
    (hhigh_error_nonneg : 0 ≤ highError)
    (hhigh_error_le_half : highError ≤ 1 / 2)
    (hlow_vS : lowPivot ≤ vS)
    (hlow_affordance : ∀ v ∈ Set.Iic lowPivot,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff ≤ lowError)
    (hfull_affordance : ∀ v ∈ Set.Ioi lowPivot,
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff)
    (hfull_capacity :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) = totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply) :
    (∫ v : ℝ,
      (Set.Iic vS).indicator
        (fun v => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff) v
      ∂valueLaw) ≤
      lowError + 2 * totalSupply * highError := by
  let p : ℝ -> ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  let fullP : ℝ -> ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseLaw))
      (Finset.univ : Finset (Fin n)) v cutoff
  have hp : Integrable p valueLaw := by
    simpa [p, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw upper cutoff)
  have hfullP : Integrable fullP valueLaw := by
    simpa [fullP, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw
        (Finset.univ : Finset (Fin n)) cutoff)
  have hp_le_one : ∀ v, p v ≤ 1 := by
    intro v
    exact cutoffAffordanceProbability_le_one
      (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  have hfullP_nonneg : ∀ v, 0 ≤ fullP v := by
    intro v
    exact cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin n => noiseLaw))
      (Finset.univ : Finset (Fin n)) v cutoff
  have hlow_integral :
      (∫ v in Set.Iic lowPivot, p v ∂valueLaw) ≤ lowError := by
    calc
      (∫ v in Set.Iic lowPivot, p v ∂valueLaw) ≤
          valueLaw.real (Set.Iic lowPivot) * lowError :=
        theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
          valueLaw p hp measurableSet_Iic (by
            intro v hv
            simpa [p] using hlow_affordance v hv)
      _ ≤ lowError := by
        have hmass : valueLaw.real (Set.Iic lowPivot) ≤ 1 :=
          measureReal_le_one (μ := valueLaw)
        nlinarith
  have hbudget := theorem1_high_interval_mass_budget
    valueLaw fullP hfullP hfullP_nonneg (le_of_eq hfull_capacity)
    (by
      intro v hv
      simpa [fullP] using hfull_affordance v hv)
    htail_normalization hlow_vS
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rw [← hfull_capacity]
    exact integral_nonneg hfullP_nonneg
  have hmiddle_mass : valueLaw.real (Set.Ioc lowPivot vS) ≤
      2 * totalSupply * highError :=
    theorem1Tail_interval_mass_le_two_mul_supply_mul_error
      htotalSupply_nonneg hhigh_error_nonneg hhigh_error_le_half hbudget
  have hmiddle_integral :
      (∫ v in Set.Ioc lowPivot vS, p v ∂valueLaw) ≤
        2 * totalSupply * highError := by
    calc
      (∫ v in Set.Ioc lowPivot vS, p v ∂valueLaw) ≤
          valueLaw.real (Set.Ioc lowPivot vS) :=
        theorem1_setIntegral_le_measureReal_of_le_one
          valueLaw p hp measurableSet_Ioc (fun v _ => hp_le_one v)
      _ ≤ 2 * totalSupply * highError := hmiddle_mass
  change (∫ v : ℝ, (Set.Iic vS).indicator p v ∂valueLaw) ≤ _
  rw [integral_indicator measurableSet_Iic]
  calc
    (∫ v in Set.Iic vS, p v ∂valueLaw) =
        (∫ v in Set.Iic lowPivot, p v ∂valueLaw) +
          ∫ v in Set.Ioc lowPivot vS, p v ∂valueLaw := by
      calc
        (∫ v in Set.Iic vS, p v ∂valueLaw) =
            ∫ v in Set.Iic lowPivot ∪ Set.Ioc lowPivot vS, p v ∂valueLaw := by
          rw [Set.Iic_union_Ioc_eq_Iic hlow_vS]
        _ = (∫ v in Set.Iic lowPivot, p v ∂valueLaw) +
              ∫ v in Set.Ioc lowPivot vS, p v ∂valueLaw :=
          setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
            hp.integrableOn hp.integrableOn
    _ ≤ lowError + 2 * totalSupply * highError := by linarith

/--
The Case 2 upper-block integral estimate with the threshold placement handled
explicitly.  If the moving pivot lies above `vS`, the full low region is
already covered by the full-maximum bound; otherwise the full-market high
endpoint controls the intervening value mass.
-/
theorem theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
    {n : ℕ} [NeZero n] (noiseLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (active : Finset (Fin n)) (cutoff : Fin n -> ℝ)
    {pivot center radius vS totalSupply lowError highError : ℝ}
    (hlow_error_nonneg : 0 ≤ lowError)
    (hhigh_error_nonneg : 0 ≤ highError)
    (hhigh_error_le_half : highError ≤ 1 / 2)
    (hlow_deviation :
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) center radius ≤ lowError)
    (hfull_affordance : ∀ v ∈ Set.Ioi (pivot - center - radius),
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff)
    (hfull_capacity :
      (∫ v : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) = totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply) :
    (∫ v : ℝ,
      (Set.Iic vS).indicator
        (fun v => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (theorem1CutoffAtOrAboveBlock active cutoff pivot) v cutoff) v
      ∂valueLaw) ≤
      lowError + 2 * totalSupply * highError := by
  let threshold : ℝ := pivot - center - radius
  let upper := theorem1CutoffAtOrAboveBlock active cutoff pivot
  let p : ℝ -> ℝ := fun v => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin n => noiseLaw)) upper v cutoff
  have hlow : ∀ v ∈ Set.Iic threshold, p v ≤ lowError := by
    intro v hv
    have hseparation : center + radius ≤ pivot - v := by
      change v ≤ pivot - center - radius at hv
      linarith
    calc
      p v ≤ AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) center radius := by
        simpa [p, upper] using
          (theorem1_iid_atOrAbove_affordance_le_full_max_deviation
            noiseLaw active cutoff pivot v center radius hseparation)
      _ ≤ lowError := hlow_deviation
  by_cases hthreshold_vS : threshold ≤ vS
  · simpa [threshold, upper, p] using
      (theorem1_largeGap_upper_affordance_low_integral_le_of_primitives
        noiseLaw valueLaw upper cutoff hlow_error_nonneg hhigh_error_nonneg
        hhigh_error_le_half hthreshold_vS
        (by
          intro v hv
          simpa [p] using hlow v hv)
        (by
          intro v hv
          simpa [threshold] using hfull_affordance v hv)
        hfull_capacity htail_normalization)
  · have hvS_threshold : vS ≤ threshold := le_of_not_ge hthreshold_vS
    have hp : Integrable p valueLaw := by
      simpa [p, cutoffAffordanceProbability] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin n => noiseLaw)) valueLaw upper cutoff)
    have hwhole_nonneg : ∀ v, 0 ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff := by
      intro v
      exact cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff
    have htotalSupply_nonneg : 0 ≤ totalSupply := by
      rw [← hfull_capacity]
      exact integral_nonneg hwhole_nonneg
    have hlow_integral :
        (∫ v in Set.Iic vS, p v ∂valueLaw) ≤ lowError := by
      calc
        (∫ v in Set.Iic vS, p v ∂valueLaw) ≤
            valueLaw.real (Set.Iic vS) * lowError :=
          theorem1_setIntegral_le_measureReal_mul_of_pointwise_le
            valueLaw p hp measurableSet_Iic (by
              intro v hv
              exact hlow v (hv.trans hvS_threshold))
        _ ≤ lowError := by
          have hmass : valueLaw.real (Set.Iic vS) ≤ 1 :=
            measureReal_le_one (μ := valueLaw)
          nlinarith
    change (∫ v : ℝ, (Set.Iic vS).indicator p v ∂valueLaw) ≤ _
    rw [integral_indicator measurableSet_Iic]
    nlinarith

end

end PG24NoisyMatchingMarkets
