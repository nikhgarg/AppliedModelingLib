import PG24NoisyMatchingMarkets.Theorem1SelectedCase1Route
import PG24NoisyMatchingMarkets.Theorem1SelectedCutoffGeometry

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The Case 2 rank-prefix split has the same checked lower-capacity term as Case
1.  The large-gap probability argument is separate; this theorem establishes
the exact selected-stable decomposition at the source rank cutoff first.
-/
theorem theorem1_selectedStable_low_matched_mass_le_rankPrefix_components_iid
    {StudentType : Type u} {C : ℕ} [MeasurableSpace StudentType]
    (M : CutoffMarket StudentType (Fin (C + 1)))
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    {matching : M.Matching} (hstable : M.Stable matching)
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin (C + 1) -> ℝ)
    (demand : StudentType × (Fin (C + 1) -> ℝ) -> Option (Fin (C + 1)))
    (alpha beta gamma : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin (C + 1) -> ℝ)) (college : Fin (C + 1)),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (hchoice_mass_eq_aggregate_demand_lower :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        demand
        (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
          (theorem3RankedCutoffNat C cutoff
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)))) =
        ∑ college ∈ theorem1CutoffBelowBlock
          (Finset.univ : Finset (Fin (C + 1))) cutoff
          (theorem3RankedCutoffNat C cutoff
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))),
          M.aggregateDemand (I.marketClearingCutoffOfStable hstable) college)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity : ∀ college ∈ (Finset.univ : Finset (Fin (C + 1))),
      M.capacity college ≤ alpha / (C : ℝ))
    {region : Set ℝ} (hregion : MeasurableSet region) :
    eventMass
        (studentLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) -> ℝ) =>
          value outcome.1 ∈ region ∧
            chosenInActive demand (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        ∫ v : ℝ,
          region.indicator
            (fun v => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1))) cutoff
                (theorem3RankedCutoffNat C cutoff
                  (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
              v cutoff) v
          ∂valueLaw := by
  let rankCut := theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)
  have hprefix : rankCut ≤ C :=
    theorem1EarlyPrefixRank_le_marketIndex hbeta hgamma hC_pos
  have hsparse_nat :
      (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff rankCut)).card ≤ rankCut := by
    simpa [rankCut, theorem3RankedCutoffNat_eq_rankedCutoff C cutoff hprefix] using
      (theorem1CutoffBelowBlock_card_le_rank_start C rankCut cutoff hprefix)
  have hprefix_real : (rankCut : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    dsimp [rankCut]
    unfold theorem3EarlyPrefixRank
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hsparse_nat_real :
      ((theorem1CutoffBelowBlock
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff rankCut)).card : ℝ) ≤
        (rankCut : ℝ) := by
    exact_mod_cast hsparse_nat
  have hsparse_real :
      ((theorem1CutoffBelowBlock
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff rankCut)).card : ℝ) ≤
        Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) :=
    hsparse_nat_real.trans hprefix_real
  exact theorem1_selectedStable_low_matched_mass_le_case1_sparse_components_iid
    (C := C) M I K hstable studentLaw value hvalue valueLaw hvalue_marginal
    noiseLaw cutoff demand (theorem3RankedCutoffNat C cutoff rankCut)
    alpha beta gamma hchosen_feasible
    (by simpa [rankCut] using hchoice_mass_eq_aggregate_demand_lower)
    (by exact_mod_cast hC_pos) halpha_nonneg hsparse_real hcapacity hregion

end

end PG24NoisyMatchingMarkets
