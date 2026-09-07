import PG24NoisyMatchingMarkets.Theorem1LargeGapQualitativeRoute
import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedCutoffBridge
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal Case 2 conclusion

This instantiates the large-gap route at literal source demand and its explicit
selected cutoff.  The conclusion is a matched-mass statement, not merely an
affordance estimate.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
On a literal source-model sequence in the actual large-gap alternative, the
low-value mass matched by the selected demand rule tends to zero.  The result
uses no raw choice-mass or clearing premise: both are derived from literal
singleton-demand semantics and literal selected-cutoff clearing.
-/
theorem theorem1_literal_selected_largeGap_low_matched_mass_tendsto_zero
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta gamma vS totalSupply : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))) :
    Tendsto (fun C : ℕ =>
      eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome))
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure (inst 0).studentLaw :=
    (inst 0).studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← (inst 0).value_marginal]
    exact Measure.isProbabilityMeasure_map
      (inst 0).value_measurable.aemeasurable
  have hfull_capacity : ∀ C : ℕ,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C).selectedCutoffVector ∂eta) = totalSupply := by
    intro C
    exact (inst C).theorem1_selected_full_affordance_integral_eq_totalSupply
  have hupper_zero :=
    theorem1_largeGap_upper_low_integral_tendsto_zero_of_beta
      noiseLaw eta hbeta hgamma hvariance hfull_capacity htail_normalization
      hlarge_gap
  have hcapacity_zero : Tendsto
      (fun C : ℕ => alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpow.const_mul alpha
  have hupper_capacity_zero : Tendsto
      (fun C : ℕ =>
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  (inst C).selectedCutoffVector
                  (theorem3RankedCutoffNat C (inst C).selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value (inst C).selectedCutoffVector) value
            ∂eta) atTop (nhds 0) := by
    simpa using hcapacity_zero.add hupper_zero
  have hcomponents : ∀ᶠ C : ℕ in atTop,
      eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  (inst C).selectedCutoffVector
                  (theorem3RankedCutoffNat C (inst C).selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value (inst C).selectedCutoffVector) value
            ∂eta := by
    filter_upwards [eventually_gt_atTop 0] with C hC_pos
    exact (inst C).theorem1_selected_low_matched_mass_le_rankPrefix_components
      hbeta.1 hgamma hC_pos halpha_nonneg measurableSet_Iic
  have hmatched_nonneg : ∀ C : ℕ,
      0 ≤ eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) := by
    intro C
    exact measureReal_nonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_capacity_zero (Filter.Eventually.of_forall hmatched_nonneg) hcomponents

end

end PG24NoisyMatchingMarkets
