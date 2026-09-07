import PG24NoisyMatchingMarkets.SourceDemandBlockMass
import PG24NoisyMatchingMarkets.Theorem1SourceModelIntegration

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The source-demand clauses give the whole-market match/affordance equivalence
used by Theorem 1.  This derives the equivalence from no-demand and feasibility
semantics instead of accepting it as an opaque matching premise.
-/
theorem theorem1_sourceDemand_chosenInAll_iff_affordance
    {StudentType : Type u} {n : ℕ}
    (value : StudentType -> ℝ) (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college) :
    ∀ outcome : StudentType × (Fin n -> ℝ),
      chosenInActive demand (Finset.univ : Finset (Fin n)) outcome ↔
        theorem1TypeNoiseAffordanceEvent value
          (Finset.univ : Finset (Fin n)) cutoff outcome := by
  simpa [theorem1TypeNoiseAffordanceEvent] using
    (sourceDemand_chosenInAll_iff_cutoffCrossed
      value cutoff demand hdemand_none_iff_no_crossed hchosen_feasible)

/--
The Theorem 1 value-marginal/Fubini identity under the actual iid source
demand semantics.  The arbitrary `StudentType` coordinate retains preferences
and any correlation they have with values.
-/
theorem theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) =
      ∫ v : ℝ,
        region.indicator
          (fun v => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw := by
  exact
    theorem1_source_model_value_restricted_matched_mass_eq_integral_affordance
      studentLaw value hvalue valueLaw hvalue_marginal
      (Measure.pi (fun _ : Fin n => noiseLaw))
      (Finset.univ : Finset (Fin n)) cutoff demand
      (theorem1_sourceDemand_chosenInAll_iff_affordance
        value cutoff demand hdemand_none_iff_no_crossed hchosen_feasible)
      hregion

/--
At an exactly clearing cutoff, whole-market iid source demand has total mass
equal to total capacity.  The only model obligations are stated as the demand
semantics and the explicit source-choice/aggregate-demand identification.
-/
theorem theorem1_sourceDemand_whole_market_matched_mass_eq_total_capacity_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
        ∑ college : Fin n, M.aggregateDemand P college) :
    (∫ v : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
      ∑ college : Fin n, M.capacity college := by
  exact
    theorem1_source_model_whole_market_matched_mass_eq_total_capacity
      M K hclearing studentLaw value hvalue valueLaw hvalue_marginal
      (Measure.pi (fun _ : Fin n => noiseLaw)) cutoff demand
      (theorem1_sourceDemand_chosenInAll_iff_affordance
        value cutoff demand hdemand_none_iff_no_crossed hchosen_feasible)
      hchoice_mass_eq_aggregate_demand

/--
The low-matched/high-unmatched tail bridge with explicit iid source demand
semantics.  This is the source-facing form that consumes a proved cutoff-tail
integral; it does not make a preference-independence assumption.
-/
theorem theorem1_sourceDemand_low_high_tail_mass_le_of_cutoff_tail_bound_iid
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin n))
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hclearing : M.MarketClearing P)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n -> ℝ)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
        ∑ college : Fin n, M.aggregateDemand P college)
    {lowValues : Set ℝ} (hlowValues : MeasurableSet lowValues)
    (hcapacity_eq_high_value_mass :
      (∑ college : Fin n, M.capacity college) = valueLaw.real lowValuesᶜ)
    {tailBound : ℝ}
    (hcutoff_tail :
      (∫ v : ℝ,
        lowValues.indicator
          (fun v => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) v cutoff) v ∂valueLaw) ≤
        tailBound) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ lowValues ∧
            chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) ≤
      tailBound ∧
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        (fun outcome : StudentType × (Fin n -> ℝ) =>
          value outcome.1 ∈ lowValuesᶜ ∧
            ¬ chosenInActive demand (Finset.univ : Finset (Fin n)) outcome) ≤
      tailBound := by
  exact
    theorem1_source_model_low_high_tail_mass_le_of_cutoff_tail_bound
      M K hclearing studentLaw value hvalue valueLaw hvalue_marginal
      (Measure.pi (fun _ : Fin n => noiseLaw)) cutoff demand
      (theorem1_sourceDemand_chosenInAll_iff_affordance
        value cutoff demand hdemand_none_iff_no_crossed hchosen_feasible)
      hchoice_mass_eq_aggregate_demand hlowValues
      hcapacity_eq_high_value_mass hcutoff_tail

end

end PG24NoisyMatchingMarkets
