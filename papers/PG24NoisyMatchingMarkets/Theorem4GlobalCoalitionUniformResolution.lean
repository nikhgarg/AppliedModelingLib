import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionAffordanceSemantics
import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionCapacityBridge
import PG24NoisyMatchingMarkets.Theorem4UniformCapacityCertificate
import Mathlib.Tactic

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

theorem eventually_theorem4_global_coalition_low_cutoff_count_of_longTailed
    {StudentSeq : ℕ → Type u} {GlobalCollegeSeq : ℕ → Type v}
    [∀ C, Fintype (GlobalCollegeSeq C)]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (GlobalCollegeSeq C))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type w}
    (selected : ∀ C : ℕ, Admissible C →
      { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (coalitionEmbedding : ∀ C : ℕ, Admissible C →
      Fin (C + 1) ↪ GlobalCollegeSeq C)
    (globalCutoff : ∀ C : ℕ,
      (Mseq C).Cutoff → GlobalCollegeSeq C → ℝ)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ,
      (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (globalChoice : ∀ C : ℕ,
      (Mseq C).Cutoff → OutcomeSeq C → Option (GlobalCollegeSeq C))
    (localCoordinates : ∀ C : ℕ, Admissible C →
      OutcomeSeq C → ℝ × (Fin (C + 1) → ℝ))
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1)
    (houtcome_finite : ∀ C : ℕ, ∀ P : (Mseq C).Cutoff,
      IsFiniteMeasure (outcomeLaw C P))
    (hchoice_mass_eq_aggregateDemand :
      ∀ C : ℕ, ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
        choiceMass (outcomeLaw C P) (globalChoice C P)
            (Finset.univ : Finset (GlobalCollegeSeq C)) =
          ∑ c : GlobalCollegeSeq C, (Mseq C).aggregateDemand P c)
    (hcapacity_sum : ∀ C : ℕ,
      (∑ c : GlobalCollegeSeq C, (Mseq C).capacity c) = totalSupply)
    (hlocalCoordinates_measurable : ∀ C : ℕ, ∀ a : Admissible C,
      Measurable (localCoordinates C a))
    (hlocalCoordinates_map : ∀ C : ℕ, ∀ a : Admissible C,
      Measure.map (localCoordinates C a)
        (outcomeLaw C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)) =
          eta.prod (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
    (hlocal_affordance_implies_global_match :
      ∀ C : ℕ, ∀ a : Admissible C, ∀ active : Finset (Fin (C + 1)),
        ∀ outcome : OutcomeSeq C,
          theorem4CoalitionAffordanceEvent active
            (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (localCoordinates C a outcome) →
              chosenInActive
                (globalChoice C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))
                (Finset.univ : Finset (GlobalCollegeSeq C)) outcome) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            (lowCutoffIndexSet
              (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
                epsilonFloorSplitIndex (tol / 2) C := by
  rcases
      exists_theorem4_uniform_low_cutoff_integral_capacity_certificate_at_vHigh_of_longTailed
        noiseLaw hlong eta htol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, huniform⟩
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  filter_upwards [huniform] with C huniformC a
  let P : (Mseq C).Cutoff :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  let localCutoff : Fin (C + 1) → ℝ :=
    coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C) P
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet localCutoff
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C)
  letI : IsFiniteMeasure (outcomeLaw C P) := houtcome_finite C P
  have hintegrated :
      epsilonFloorSplitIndex (tol / 2) C < active.card →
        totalSupply <
          ∫ value : ℝ,
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              active value localCutoff ∂eta := by
    intro htoo_many
    simpa [active, cutoffAffordanceProbability] using
      (huniformC localCutoff (by simpa [active] using htoo_many))
  have hbridge :
      ∃ event : OutcomeSeq C → Prop,
        (∫ value : ℝ,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active value localCutoff ∂eta) ≤
          eventMass (outcomeLaw C P) event ∧
          (∀ outcome : OutcomeSeq C, event outcome →
            chosenInActive (globalChoice C P)
              (Finset.univ : Finset (GlobalCollegeSeq C)) outcome) := by
    simpa [cutoffAffordanceProbability] using
      (theorem4_integrated_coalition_affordance_global_match_witness
        eta noiseLaw (outcomeLaw C P) (globalChoice C P)
        (localCoordinates C a) (hlocalCoordinates_measurable C a)
        (hlocalCoordinates_map C a) active localCutoff (by
          intro outcome hlocal
          exact hlocal_affordance_implies_global_match C a active outcome
            (by simpa [P, localCutoff] using hlocal)))
  have hcount :=
    localLowCutoff_card_le_of_global_integrated_capacity
      (Iseq C) (Kseq C) (selected C a) (coalitionEmbedding C a)
      (globalCutoff C) noiseLaw eta (outcomeLaw C) (globalChoice C)
      (floor := vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (totalSupply := totalSupply)
      (splitIndex := epsilonFloorSplitIndex (tol / 2) C)
      (houtcome_finite C) (hchoice_mass_eq_aggregateDemand C)
      (hcapacity_sum C) (by
        simpa [P, localCutoff, active] using hintegrated) (by
        simpa [P, localCutoff, active] using hbridge)
  simpa [P, localCutoff, active] using hcount

end

end PG24NoisyMatchingMarkets
