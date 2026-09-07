import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionEtaEndpoint
import Mathlib.Tactic

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

theorem theorem4_global_coalition_amplification_source_shaped_of_longTailed_eta
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
    (globalScore : ∀ C : ℕ,
      (Mseq C).Cutoff → OutcomeSeq C → GlobalCollegeSeq C → ℝ)
    (localCoordinates : ∀ C : ℕ, Admissible C →
      OutcomeSeq C → ℝ × (Fin (C + 1) → ℝ))
    {totalSupply : ℝ}
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
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
    (hcoalition_score :
      ∀ C : ℕ, ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
        ∀ outcome : OutcomeSeq C, ∀ c : Fin (C + 1),
          globalScore C P outcome (coalitionEmbedding C a c) =
            (localCoordinates C a outcome).1 +
              (localCoordinates C a outcome).2 c)
    (hunmatched_iff_no_global_affordance :
      ∀ C : ℕ, ∀ P : (Mseq C).Cutoff, ∀ outcome : OutcomeSeq C,
        globalChoice C P outcome = none ↔
          ¬ cutoffCrossed (globalScore C P outcome) (globalCutoff C P)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ effectiveSupply : ℝ,
          ∃ largeSubset : Finset (Fin (C + 1)),
          ∃ regularSet : Set ℝ,
            CoalitionLargeSubset
                (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
              eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    largeSubset value
                    (coalitionCutoffRestriction (coalitionEmbedding C a)
                      (globalCutoff C)
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := (selected C a).1) (selected C a).2)) -
                  effectiveSupply| < epsilon) := by
  intro epsilon hepsilon_pos
  rcases exists_theorem4_global_coalition_nonLow_endpoint_of_longTailed_eta
      Mseq Iseq Kseq selected coalitionEmbedding globalCutoff noiseLaw eta hlong
      outcomeLaw globalChoice globalScore localCoordinates hepsilon_pos
      htotalSupply_lt_one houtcome_finite hchoice_mass_eq_aggregateDemand
      hcapacity_sum hlocalCoordinates_measurable hlocalCoordinates_map
      hcoalition_score hunmatched_iff_no_global_affordance with
    ⟨vLow, vHigh, sigma, valueFloor, endpointEpsilon, hv, hsigma_pos,
      hvalueFloor_lt, hendpointEpsilon_pos, hendpointEpsilon_le_one,
      hregular_exception, hlarge, hmass, hclose⟩
  filter_upwards [hlarge, hclose] with C hlargeC hcloseC a
  refine
    ⟨cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (nonLowCutoffIndexSet
          (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
        vLow
        (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)),
      nonLowCutoffIndexSet
        (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (vHigh + theorem4HighTailQuantile noiseLaw sigma C),
      Set.Icc vLow vHigh, hlargeC a, hregular_exception, ?_⟩
  intro value hvalue
  exact hcloseC a value hvalue

end

end PG24NoisyMatchingMarkets
