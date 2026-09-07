import PG24NoisyMatchingMarkets.Theorem1SourceDemandDecomposition
import PG24NoisyMatchingMarkets.Theorem1SourceProofHelpers

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The selected-stable version of the source Case 1 decomposition.  The full
low-value matched mass is split at the actual cutoff pivot into a lower block
controlled by clearing capacity and an upper block controlled by its genuine
affordance probability.
-/
theorem theorem1_selectedStable_low_matched_mass_le_case1_components_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (pivot : ℝ)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand_lower :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot) =
        ∑ college ∈
          theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot,
          M.aggregateDemand
            (I.marketClearingCutoffOfStable hstable) college)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) ≤
      activeCapacity
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
        M.capacity +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin n)) cutoff pivot)
              v cutoff) v
          ∂valueLaw := by
  exact
    theorem1_sourceDemand_value_restricted_matched_mass_le_lower_capacity_add_upper_affordance_iid
      M K (I.marketClearingCutoffOfStable_marketClearing hstable)
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw cutoff demand
      (Finset.univ : Finset (Fin n))
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
      (theorem1CutoffAtOrAboveBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
      (theorem1CutoffBelowBlock_union_atOrAboveBlock
        (Finset.univ : Finset (Fin n)) cutoff pivot)
      hchosen_feasible hchoice_mass_eq_aggregate_demand_lower hregion

/--
Case 1's sparse lower cutoff block has the source polynomial capacity rate.
This combines the semantic selected-stable decomposition with the checked
finite capacity calculation, while leaving the upper-block analytic estimate
as a separate proved input.
-/
theorem theorem1_selectedStable_low_matched_mass_le_case1_sparse_components_iid
    {StudentType : Type u} {n C : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (pivot alpha beta gamma : ℝ)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand_lower :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot) =
        ∑ college ∈
          theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot,
          M.aggregateDemand
            (I.marketClearingCutoffOfStable hstable) college)
    (hC_pos : 0 < (C : ℝ)) (halpha_nonneg : 0 ≤ alpha)
    (hsparse :
      ((theorem1CutoffBelowBlock
        (Finset.univ : Finset (Fin n)) cutoff pivot).card : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma))
    (hcapacity : ∀ college ∈ (Finset.univ : Finset (Fin n)),
      M.capacity college ≤ alpha / (C : ℝ))
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin n)) cutoff pivot)
              v cutoff) v
          ∂valueLaw := by
  have hcomponents :=
    theorem1_selectedStable_low_matched_mass_le_case1_components_iid
      M I K hstable studentLaw value hvalue valueLaw hvalue_marginal noiseLaw
      cutoff demand pivot hchosen_feasible hchoice_mass_eq_aggregate_demand_lower
      hregion
  have hcapacity_sparse :
      activeCapacity
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
        M.capacity ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    apply theorem1Tail_sparseBlock_capacity_le_alpha_rpow_neg_K
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
      M.capacity (C := C) hC_pos halpha_nonneg hsparse
    intro college hcollege
    exact hcapacity college (Finset.mem_filter.mp hcollege).1
  calc
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) ≤
        activeCapacity
          (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin n)) cutoff pivot)
          M.capacity +
          ∫ v : ℝ,
            region.indicator
              (fun v => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin n)) cutoff pivot)
                v cutoff) v
            ∂valueLaw := hcomponents
    _ ≤ alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ v : ℝ,
            region.indicator
              (fun v => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin n => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin n)) cutoff pivot)
                v cutoff) v
            ∂valueLaw := by
      gcongr

end

end PG24NoisyMatchingMarkets
