import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionAEMatchSemantics
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Explicit Selected-Cutoff Capacity Bridge

The generic cutoff interface chooses a representative cutoff noncomputably.
The extended source theorem instead starts with one selected stable matching
and its stated market-clearing cutoff.  These lemmas carry that explicit
cutoff through the global-capacity contradiction.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w

/--
An almost-everywhere globally matched event has mass at most total capacity at
an explicitly supplied market-clearing cutoff.
-/
theorem theorem4_eventMass_le_global_totalSupply_at_explicit_cutoff_ae
    {Student : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hP : M.MarketClearing P)
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome)
    (chosenCollege : Outcome → Option GlobalCollege)
    {event : Outcome → Prop} {totalSupply : ℝ}
    [IsFiniteMeasure outcomeLaw]
    (hchoice_mass_eq_aggregateDemand :
      choiceMass outcomeLaw chosenCollege
          (Finset.univ : Finset GlobalCollege) =
        ∑ c : GlobalCollege, M.aggregateDemand P c)
    (hcapacity_sum : (∑ c : GlobalCollege, M.capacity c) = totalSupply)
    (hevent_matched_globally :
      ∀ᵐ outcome ∂outcomeLaw, event outcome →
        chosenInActive chosenCollege (Finset.univ : Finset GlobalCollege) outcome) :
    eventMass outcomeLaw event ≤ totalSupply := by
  calc
    eventMass outcomeLaw event ≤
        choiceMass outcomeLaw chosenCollege (Finset.univ : Finset GlobalCollege) :=
      theorem4_eventMass_mono_ae outcomeLaw hevent_matched_globally
    _ = ∑ c : GlobalCollege, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregateDemand
    _ = ∑ c : GlobalCollege, M.capacity c := by
      exact Finset.sum_congr rfl (fun c _ =>
        K.marketClearing_aggregateDemand_eq_capacity P hP c)
    _ = totalSupply := hcapacity_sum

/--
The local low-cutoff count bound at an explicit source-selected stable cutoff.
The selected matching's evaluator is passed directly as `chosenCollege`, so
the capacity argument does not use a cutoff chosen by `Classical.choose`.
-/
theorem theorem4_localLowCutoff_card_le_of_explicit_integrated_capacity_ae
    {C : ℕ} {Student : Type u} {GlobalCollege : Type v}
    [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (K : MarketClearingCapacityInterface M)
    {P : M.Cutoff} (hP : M.MarketClearing P)
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : M.Cutoff → GlobalCollege → ℝ)
    (noiseLaw valueLaw : Measure ℝ)
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome)
    (chosenCollege : Outcome → Option GlobalCollege)
    {floor totalSupply : ℝ} {splitIndex : ℕ}
    [IsFiniteMeasure outcomeLaw]
    (hchoice_mass_eq_aggregateDemand :
      choiceMass outcomeLaw chosenCollege
          (Finset.univ : Finset GlobalCollege) =
        ∑ c : GlobalCollege, M.aggregateDemand P c)
    (hcapacity_sum : (∑ c : GlobalCollege, M.capacity c) = totalSupply)
    (hintegrated_crossing :
      splitIndex <
          (lowCutoffIndexSet
            (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
            floor).card →
        totalSupply <
          ∫ value : ℝ,
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (lowCutoffIndexSet
                (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
                floor)
              value
              (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
              ∂valueLaw)
    (hintegrated_affordance_global_match :
      ∃ event : Outcome → Prop,
        (∫ value : ℝ,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (lowCutoffIndexSet
              (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
              floor)
            value
            (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
            ∂valueLaw) ≤ eventMass outcomeLaw event ∧
        (∀ᵐ outcome ∂outcomeLaw, event outcome →
          chosenInActive chosenCollege
            (Finset.univ : Finset GlobalCollege) outcome)) :
    (lowCutoffIndexSet
      (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
      floor).card ≤ splitIndex := by
  by_contra hnot
  have htoo_many : splitIndex <
      (lowCutoffIndexSet
        (coalitionCutoffRestriction coalitionEmbedding globalCutoff P)
        floor).card :=
    Nat.lt_of_not_ge hnot
  have hcross := hintegrated_crossing htoo_many
  rcases hintegrated_affordance_global_match with
    ⟨event, hintegral_le_event, hevent_matched_globally⟩
  have hevent_le_supply : eventMass outcomeLaw event ≤ totalSupply :=
    theorem4_eventMass_le_global_totalSupply_at_explicit_cutoff_ae
      K hP outcomeLaw chosenCollege hchoice_mass_eq_aggregateDemand
      hcapacity_sum hevent_matched_globally
  linarith

end

end PG24NoisyMatchingMarkets
