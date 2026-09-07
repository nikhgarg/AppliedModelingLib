import PG24NoisyMatchingMarkets.Theorem4GlobalChoiceSemantics
import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionCapacityBridge
import Mathlib.Tactic

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- Event mass is monotone under an almost-everywhere implication. -/
theorem theorem4_eventMass_mono_ae
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsFiniteMeasure outcomeLaw]
    {left right : Outcome → Prop}
    (himp : ∀ᵐ outcome ∂outcomeLaw, left outcome → right outcome) :
    eventMass outcomeLaw left ≤ eventMass outcomeLaw right := by
  unfold eventMass AppliedModelingLib.measureProb
  exact ENNReal.toReal_mono (measure_ne_top outcomeLaw {outcome | right outcome})
    (measure_mono_ae himp)

/--
The extended source model's common coalition value is only required almost
everywhere under the student law.  This derives the affordability-to-global
match implication on that same almost-everywhere domain.
-/
theorem theorem4_local_affordance_implies_global_match_ae_of_unmatched_iff_no_global_affordance
    {C : ℕ} {Outcome GlobalCollege : Type*} [MeasurableSpace Outcome]
    [Fintype GlobalCollege]
    (outcomeLaw : Measure Outcome)
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : GlobalCollege → ℝ)
    (globalScore : Outcome → GlobalCollege → ℝ)
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hcoalition_score :
      ∀ᵐ outcome ∂outcomeLaw, ∀ c : Fin (C + 1),
        globalScore outcome (coalitionEmbedding c) =
          (localCoordinates outcome).1 + (localCoordinates outcome).2 c)
    (hunmatched_iff_no_global_affordance :
      ∀ outcome : Outcome,
        globalChoice outcome = none ↔
          ¬ cutoffCrossed (globalScore outcome) globalCutoff)
    (active : Finset (Fin (C + 1)))
    (localCutoff : Fin (C + 1) → ℝ)
    (hlocalCutoff :
      ∀ c : Fin (C + 1),
        localCutoff c = globalCutoff (coalitionEmbedding c)) :
    ∀ᵐ outcome ∂outcomeLaw,
      theorem4CoalitionAffordanceEvent active localCutoff
          (localCoordinates outcome) →
        chosenInActive globalChoice
          (Finset.univ : Finset GlobalCollege) outcome := by
  filter_upwards [hcoalition_score] with outcome hscore hlocal
  rcases hlocal with ⟨c, hc, hcross⟩
  have hglobal_cross : cutoffCrossed (globalScore outcome) globalCutoff := by
    refine ⟨coalitionEmbedding c, ?_⟩
    calc
      globalCutoff (coalitionEmbedding c) = localCutoff c :=
        (hlocalCutoff c).symm
      _ < (localCoordinates outcome).1 + (localCoordinates outcome).2 c :=
        hcross
      _ = globalScore outcome (coalitionEmbedding c) :=
        (hscore c).symm
  cases hchoice : globalChoice outcome with
  | none =>
      exact False.elim
        ((hunmatched_iff_no_global_affordance outcome).mp hchoice hglobal_cross)
  | some college =>
      exact ⟨college, Finset.mem_univ _, hchoice⟩

/--
The projected iid affordability mass is bounded by global matched mass when
coalition-score agreement holds almost everywhere.  This is the measure-level
form required by the source's rho-a.e. common-value condition.
-/
theorem theorem4_integrated_coalition_affordance_le_global_matched_mass_ae
    {C : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsFiniteMeasure outcomeLaw]
    {GlobalCollege : Type*} [Fintype GlobalCollege]
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hlocalCoordinates_measurable : Measurable localCoordinates)
    (hlocalCoordinates_map :
      Measure.map localCoordinates outcomeLaw =
        valueLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ)
    (hlocal_affordance_implies_global_match :
      ∀ᵐ outcome ∂outcomeLaw,
        theorem4CoalitionAffordanceEvent active cutoff (localCoordinates outcome) →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) :
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) ≤
      eventMass outcomeLaw
        (chosenInActive globalChoice (Finset.univ : Finset GlobalCollege)) := by
  calc
    (∫ value : ℝ,
      cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
        ∂valueLaw) =
        eventMass outcomeLaw
          (fun outcome => theorem4CoalitionAffordanceEvent active cutoff
            (localCoordinates outcome)) :=
      theorem4_integrated_coalition_affordance_eq_projected_event_mass
        valueLaw noiseLaw outcomeLaw localCoordinates
        hlocalCoordinates_measurable hlocalCoordinates_map active cutoff
    _ ≤ eventMass outcomeLaw
        (chosenInActive globalChoice (Finset.univ : Finset GlobalCollege)) :=
      theorem4_eventMass_mono_ae outcomeLaw hlocal_affordance_implies_global_match

/--
The a.e. affordability-to-match bridge in the event-witness shape used by the
global capacity contradiction.
-/
theorem theorem4_integrated_coalition_affordance_global_match_witness_ae
    {C : ℕ}
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : Measure Outcome) [IsFiniteMeasure outcomeLaw]
    {GlobalCollege : Type*} [Fintype GlobalCollege]
    (globalChoice : Outcome → Option GlobalCollege)
    (localCoordinates : Outcome → ℝ × (Fin (C + 1) → ℝ))
    (hlocalCoordinates_measurable : Measurable localCoordinates)
    (hlocalCoordinates_map :
      Measure.map localCoordinates outcomeLaw =
        valueLaw.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (active : Finset (Fin (C + 1))) (cutoff : Fin (C + 1) → ℝ)
    (hlocal_affordance_implies_global_match :
      ∀ᵐ outcome ∂outcomeLaw,
        theorem4CoalitionAffordanceEvent active cutoff (localCoordinates outcome) →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) :
    ∃ event : Outcome → Prop,
      (∫ value : ℝ,
        cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) active value cutoff
          ∂valueLaw) ≤ eventMass outcomeLaw event ∧
        (∀ᵐ outcome ∂outcomeLaw, event outcome →
          chosenInActive globalChoice (Finset.univ : Finset GlobalCollege) outcome) := by
  refine ⟨fun outcome => theorem4CoalitionAffordanceEvent active cutoff
    (localCoordinates outcome), ?_, hlocal_affordance_implies_global_match⟩
  exact le_of_eq
    (theorem4_integrated_coalition_affordance_eq_projected_event_mass
      valueLaw noiseLaw outcomeLaw localCoordinates
      hlocalCoordinates_measurable hlocalCoordinates_map active cutoff)

/--
An event that is globally matched almost everywhere has mass at most total
global capacity at the selected stable cutoff.
-/
theorem theorem4_eventMass_le_global_totalSupply_of_selectedStable_ae
    {Student : Type u} {GlobalCollege : Type v} [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    (selected : { μ : M.Matching // M.Stable μ })
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : M.Cutoff → Measure Outcome)
    (chosenCollege : M.Cutoff → Outcome → Option GlobalCollege)
    {event : Outcome → Prop} {totalSupply : ℝ}
    (houtcome_finite : ∀ P : M.Cutoff,
      IsFiniteMeasure (outcomeLaw P))
    (hchoice_mass_eq_aggregateDemand :
      ∀ P : M.Cutoff, M.MarketClearing P →
        choiceMass (outcomeLaw P) (chosenCollege P)
            (Finset.univ : Finset GlobalCollege) =
          ∑ c : GlobalCollege, M.aggregateDemand P c)
    (hcapacity_sum : (∑ c : GlobalCollege, M.capacity c) = totalSupply)
    (hevent_matched_globally :
      ∀ᵐ outcome ∂outcomeLaw
        (I.marketClearingCutoffOfStable (μ := selected.1) selected.2),
        event outcome →
          chosenInActive
            (chosenCollege
              (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
            (Finset.univ : Finset GlobalCollege) outcome) :
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
  letI : IsFiniteMeasure (outcomeLaw P) := houtcome_finite P
  calc
    eventMass (outcomeLaw P) event ≤
        choiceMass (outcomeLaw P) (chosenCollege P)
          (Finset.univ : Finset GlobalCollege) :=
      theorem4_eventMass_mono_ae (outcomeLaw P) (by
        simpa [P] using hevent_matched_globally)
    _ = ∑ c : GlobalCollege, M.aggregateDemand P c :=
      hchoice_mass_eq_aggregateDemand P hP
    _ = ∑ c : GlobalCollege, M.capacity c := by
      exact Finset.sum_congr rfl (fun c _ =>
        K.marketClearing_aggregateDemand_eq_capacity P hP c)
    _ = totalSupply := hcapacity_sum

/--
The global integrated-capacity contradiction remains valid when the local
coalition-to-global-match implication holds only almost everywhere.
-/
theorem theorem4_localLowCutoff_card_le_of_global_integrated_capacity_ae
    {C : ℕ} {Student : Type u} {GlobalCollege : Type v}
    [Fintype GlobalCollege]
    {M : CutoffMarket Student GlobalCollege}
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    (selected : { μ : M.Matching // M.Stable μ })
    (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
    (globalCutoff : M.Cutoff → GlobalCollege → ℝ)
    (noiseLaw : Measure ℝ)
    (valueLaw : Measure ℝ)
    {Outcome : Type w} [MeasurableSpace Outcome]
    (outcomeLaw : M.Cutoff → Measure Outcome)
    (chosenCollege : M.Cutoff → Outcome → Option GlobalCollege)
    {floor totalSupply : ℝ} {splitIndex : ℕ}
    (houtcome_finite : ∀ P : M.Cutoff,
      IsFiniteMeasure (outcomeLaw P))
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
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (lowCutoffIndexSet
              (coalitionCutoffRestriction coalitionEmbedding globalCutoff
                (I.marketClearingCutoffOfStable (μ := selected.1) selected.2))
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
        (∀ᵐ outcome ∂outcomeLaw
          (I.marketClearingCutoffOfStable (μ := selected.1) selected.2),
          event outcome →
            chosenInActive
              (chosenCollege
                (I.marketClearingCutoffOfStable
                  (μ := selected.1) selected.2))
              (Finset.univ : Finset GlobalCollege) outcome)) :
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
    theorem4_eventMass_le_global_totalSupply_of_selectedStable_ae
      I K selected outcomeLaw chosenCollege houtcome_finite
      hchoice_mass_eq_aggregateDemand hcapacity_sum hevent_matched_globally
  linarith

end

end PG24NoisyMatchingMarkets
