import PG24NoisyMatchingMarkets.Assumptions
import Mathlib.Tactic

/-!
# Theorem 4 Global Coalition Capacity Bridge

The extended PG24 model distinguishes a coalition from the broader matching
market.  This module keeps that distinction explicit: local coalition
coordinates are embedded into a finite global college carrier, while the
capacity contradiction is taken over all globally matched outcomes.
-/

open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u v w

/-- Restrict a global cutoff vector to the enumerated coalition. -/
def coalitionCutoffRestriction
    {C : ℕ} {GlobalCollege : Type v} {Student : Type u}
    {M : CutoffMarket Student GlobalCollege}
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : M.Cutoff → GlobalCollege → ℝ)
    (P : M.Cutoff) :
    Fin (C + 1) → ℝ :=
  fun c => globalCutoff P (coalitionEmbedding c)

/--
An event whose outcomes are matched somewhere in a finite global market has
mass at most that market's total capacity at a selected stable cutoff.

The event need not say that its outcomes choose inside the coalition.  This is
the distinction needed for a coalition in a broader economy.
-/
theorem eventMass_le_global_totalSupply_of_selectedStable
    {Student : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    (selected : { μ : M.Matching // M.Stable μ })
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : M.Cutoff → MeasureTheory.Measure Outcome)
    (chosenCollege : M.Cutoff → Outcome → Option GlobalCollege)
    {event : Outcome → Prop} {totalSupply : ℝ}
    (houtcome_finite : ∀ P : M.Cutoff,
      MeasureTheory.IsFiniteMeasure (outcomeLaw P))
    (hchoice_mass_eq_aggregateDemand :
      ∀ P : M.Cutoff, M.MarketClearing P →
        choiceMass (outcomeLaw P) (chosenCollege P)
            (Finset.univ : Finset GlobalCollege) =
          ∑ c : GlobalCollege, M.aggregateDemand P c)
    (hcapacity_sum : (∑ c : GlobalCollege, M.capacity c) = totalSupply)
    (hevent_matched_globally :
      ∀ omega : Outcome, event omega →
        chosenInActive
          (chosenCollege
            (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
          (Finset.univ : Finset GlobalCollege) omega) :
    eventMass
        (outcomeLaw
          (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
        event ≤ totalSupply := by
  classical
  let P : M.Cutoff :=
    I.marketClearingCutoffOfStable (μ := selected.1) selected.2
  have hP : M.MarketClearing P :=
    I.marketClearingCutoffOfStable_marketClearing
      (μ := selected.1) selected.2
  haveI : MeasureTheory.IsFiniteMeasure (outcomeLaw P) := houtcome_finite P
  calc
    eventMass (outcomeLaw P) event ≤ ∑ c : GlobalCollege, M.capacity c := by
      apply eventMass_le_totalCapacity_of_imp_aggregateDemand_eq_capacity
        (outcomeLaw P) (chosenCollege P)
      · simpa [P] using hevent_matched_globally
      · simpa using hchoice_mass_eq_aggregateDemand P hP
      · intro c
        exact K.marketClearing_aggregateDemand_eq_capacity P hP c
    _ = totalSupply := hcapacity_sum

/--
If a local coalition block would have integrated affordability mass above the
global supply, and coalition affordability leads to a match somewhere in the
global market, that local low-cutoff block cannot be too large.

The local cutoff vector is the restriction of a global cutoff vector along the
given coalition embedding.  No claim is made that an applicant who can afford
a coalition college chooses a college in that coalition.
-/
theorem localLowCutoff_card_le_of_global_integrated_capacity
    {C : ℕ} {Student : Type u} {GlobalCollege : Type v}
    [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    (selected : { μ : M.Matching // M.Stable μ })
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : M.Cutoff → GlobalCollege → ℝ)
    (noiseLaw : MeasureTheory.Measure ℝ)
    (valueLaw : MeasureTheory.Measure ℝ)
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : M.Cutoff → MeasureTheory.Measure Outcome)
    (chosenCollege : M.Cutoff → Outcome → Option GlobalCollege)
    {floor totalSupply : ℝ} {splitIndex : ℕ}
    (houtcome_finite : ∀ P : M.Cutoff,
      MeasureTheory.IsFiniteMeasure (outcomeLaw P))
    (hchoice_mass_eq_aggregateDemand :
      ∀ P : M.Cutoff, M.MarketClearing P →
        choiceMass (outcomeLaw P) (chosenCollege P)
            (Finset.univ : Finset GlobalCollege) =
          ∑ c : GlobalCollege, M.aggregateDemand P c)
    (hcapacity_sum : (∑ c : GlobalCollege, M.capacity c) = totalSupply)
    (hintegrated_crossing :
      splitIndex <
          (lowCutoffIndexSet
            (coalitionCutoffRestriction coalitionEmbedding globalCutoff
              (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
            floor).card →
        totalSupply <
          ∫ value : ℝ,
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi
                (fun _ : Fin (C + 1) => noiseLaw))
              (lowCutoffIndexSet
                (coalitionCutoffRestriction coalitionEmbedding globalCutoff
                  (I.marketClearingCutoffOfStable
                    (μ := selected.1) selected.2))
                floor)
              value
              (coalitionCutoffRestriction coalitionEmbedding globalCutoff
                (I.marketClearingCutoffOfStable
                  (μ := selected.1) selected.2))
              ∂valueLaw)
    (hintegrated_affordance_global_match :
      ∃ event : Outcome → Prop,
        (∫ value : ℝ,
          cutoffAffordanceProbability
            (MeasureTheory.Measure.pi
              (fun _ : Fin (C + 1) => noiseLaw))
            (lowCutoffIndexSet
              (coalitionCutoffRestriction coalitionEmbedding globalCutoff
                (I.marketClearingCutoffOfStable
                  (μ := selected.1) selected.2))
              floor)
            value
            (coalitionCutoffRestriction coalitionEmbedding globalCutoff
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2))
            ∂valueLaw) ≤
          eventMass
            (outcomeLaw
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2)) event ∧
        (∀ omega : Outcome, event omega →
          chosenInActive
            (chosenCollege
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2))
            (Finset.univ : Finset GlobalCollege) omega)) :
    (lowCutoffIndexSet
      (coalitionCutoffRestriction coalitionEmbedding globalCutoff
        (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
      floor).card ≤ splitIndex := by
  classical
  by_contra hnot
  have htoo_many : splitIndex <
      (lowCutoffIndexSet
        (coalitionCutoffRestriction coalitionEmbedding globalCutoff
          (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
        floor).card :=
    Nat.lt_of_not_ge hnot
  have hcross := hintegrated_crossing htoo_many
  rcases hintegrated_affordance_global_match with
    ⟨event, hintegral_le_event, hevent_matched_globally⟩
  have hevent_le_supply :
      eventMass
          (outcomeLaw
            (I.marketClearingCutoffOfStable
              (μ := selected.1) selected.2))
          event ≤ totalSupply :=
    eventMass_le_global_totalSupply_of_selectedStable
      I K selected outcomeLaw chosenCollege houtcome_finite
      hchoice_mass_eq_aggregateDemand hcapacity_sum hevent_matched_globally
  linarith

end PG24NoisyMatchingMarkets
