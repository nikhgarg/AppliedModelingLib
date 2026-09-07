import PG24NoisyMatchingMarkets.Theorem1DenseCaseAnalytic
import PG24NoisyMatchingMarkets.Theorem1SelectedCutoffGeometry
import PG24NoisyMatchingMarkets.Theorem1SourceDemandBridge

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
At a selected stable cutoff, explicit iid source demand and clearing identify
the full cutoff-affordance integral with the source aggregate supply.
-/
theorem theorem1_selectedStable_full_affordance_integral_eq_totalSupply_iid
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
        ∑ college : Fin n,
          M.aggregateDemand (I.marketClearingCutoffOfStable hstable) college)
    (totalSupply : ℝ)
    (hcapacity_sum : (∑ college : Fin n, M.capacity college) = totalSupply) :
    (∫ v : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) = totalSupply := by
  calc
    (∫ v : ℝ,
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff ∂valueLaw) =
        ∑ college : Fin n, M.capacity college :=
      theorem1_sourceDemand_whole_market_matched_mass_eq_total_capacity_iid
        M K (I.marketClearingCutoffOfStable_marketClearing hstable)
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw cutoff demand
        hdemand_none_iff_no_crossed hchosen_feasible
        hchoice_mass_eq_aggregate_demand
    _ = totalSupply := hcapacity_sum

end

end PG24NoisyMatchingMarkets
