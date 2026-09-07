import PG24NoisyMatchingMarkets.Theorem1PointwiseAttenuationClosure
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal attenuation conclusion

This isolates the source-semantic final step.  Once the literal selected
matching mass below the supply threshold is known to vanish, source demand
semantics and clearing yield the two pointwise attenuation limits.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
For literal basic-model selected cutoffs, a vanishing low-value matched mass
implies the source pointwise attenuation conclusion.  Positivity of the
intervening value intervals is derived from the stated connected support and
Holder regularity, and the high-side integral is obtained from literal
clearing conservation.
-/
theorem theorem1_literal_selected_attenuationConclusion_of_low_matched_mass_tendsto_zero
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {alpha totalSupply vS : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hmatched : Tendsto (fun C : ℕ =>
      eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome))
      atTop (nhds 0)) :
    theorem1_attenuationConclusion
      (fun C : ℕ => fun value : ℝ => cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        (inst C).selectedCutoffVector)
      vS := by
  letI : IsProbabilityMeasure (inst 0).studentLaw :=
    (inst 0).studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← (inst 0).value_marginal]
    exact Measure.isProbabilityMeasure_map
      (inst 0).value_measurable.aemeasurable
  have hlow_integral : Tendsto (fun C : ℕ =>
      ∫ value : ℝ,
        (Set.Iic vS).indicator
          (fun value => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) value
            (inst C).selectedCutoffVector) value
        ∂eta) atTop (nhds 0) := by
    refine hmatched.congr fun C => ?_
    letI : IsProbabilityMeasure (inst C).studentLaw :=
      (inst C).studentLaw_isProbability
    exact theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
      (inst C).studentLaw (inst C).value (inst C).value_measurable eta
      (inst C).value_marginal noiseLaw (inst C).selectedCutoffVector
      ((inst C).literal.demand.demandAt (inst C).literal.selectedCutoff)
      (inst C).selected_demand_none_iff_no_crossed
      (inst C).selected_demand_feasible measurableSet_Iic
  have hhigh_integral : Tendsto (fun C : ℕ =>
      ∫ value : ℝ,
        (Set.Ioi vS).indicator
          (fun value => 1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) value
            (inst C).selectedCutoffVector) value
        ∂eta) atTop (nhds 0) := by
    refine hmatched.congr fun C => ?_
    letI : IsProbabilityMeasure (inst C).studentLaw :=
      (inst C).studentLaw_isProbability
    calc
      eventMass
          ((inst C).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
            (inst C).value outcome.1 ∈ Set.Iic vS ∧
              chosenInActive
                ((inst C).literal.demand.demandAt
                  (inst C).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) =
        eventMass
          ((inst C).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
            (inst C).value outcome.1 ∈ Set.Ioi vS ∧
              ¬ chosenInActive
                ((inst C).literal.demand.demandAt
                  (inst C).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) :=
          (inst C).theorem1_selected_low_matched_mass_eq_high_unmatched_mass
            vS htail_normalization
      _ = ∫ value : ℝ,
          (Set.Ioi vS).indicator
            (fun value => 1 - cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) value
              (inst C).selectedCutoffVector) value
          ∂eta := by
        exact theorem1_source_model_value_restricted_unmatched_mass_eq_integral_affordance_complement
          (inst C).studentLaw (inst C).value (inst C).value_measurable eta
          (inst C).value_marginal
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (inst C).selectedCutoffVector
          ((inst C).literal.demand.demandAt (inst C).literal.selectedCutoff)
          (inst C).theorem1_selected_chosenInAll_iff_affordance
          measurableSet_Ioi
  constructor
  · intro value hvalue
    exact theorem1_low_pointwise_tendsto_zero_of_low_integral
      eta noiseLaw hvalue
      (theorem1_low_interval_mass_pos_of_connected_support eta hconnected hregular
        htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue)
      hlow_integral
  · intro value hvalue
    exact theorem1_high_pointwise_tendsto_one_of_high_unmatched_integral
      eta noiseLaw hvalue
      (theorem1_high_interval_mass_pos_of_connected_support eta hconnected hregular
        htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue)
      hhigh_integral

end

end PG24NoisyMatchingMarkets
