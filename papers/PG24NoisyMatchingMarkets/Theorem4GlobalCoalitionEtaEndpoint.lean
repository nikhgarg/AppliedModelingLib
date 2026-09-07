import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionEndpointResolution
import Mathlib.Tactic

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

theorem exists_theorem4_global_coalition_nonLow_endpoint_of_longTailed_eta
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
    {totalSupply tol : ℝ}
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
    ∃ vLow vHigh sigma valueFloor epsilon : ℝ,
      vLow < vHigh ∧ 0 < sigma ∧ valueFloor < vHigh ∧
        0 < epsilon ∧ epsilon ≤ 1 ∧
        eta.real (Set.Icc vLow vHigh)ᶜ ≤ tol ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1)))
              (nonLowCutoffIndexSet
                (coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))
                (vHigh + theorem4HighTailQuantile noiseLaw sigma C)) tol) ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            1 - tol < eta.real (Set.Icc vLow vHigh)) ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C, ∀ value ∈ Set.Icc vLow vHigh,
            |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (coalitionCutoffRestriction (coalitionEmbedding C a)
                    (globalCutoff C)
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
                value
                (coalitionCutoffRestriction (coalitionEmbedding C a)
                  (globalCutoff C)
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (coalitionCutoffRestriction (coalitionEmbedding C a)
                    (globalCutoff C)
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
                vLow
                (coalitionCutoffRestriction (coalitionEmbedding C a)
                  (globalCutoff C)
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  have hhalf_tol_pos : 0 < tol / 2 := by
    linarith
  rcases exists_regular_interval_measure_compl_le_of_probability eta hhalf_tol_pos with
    ⟨vLow, vHigh, hv, hsmall_half⟩
  have hsmall : eta.real (Set.Icc vLow vHigh)ᶜ ≤ tol := by
    linarith
  have hpartition :
      eta.real (Set.Icc vLow vHigh) + eta.real (Set.Icc vLow vHigh)ᶜ = 1 := by
    calc
      eta.real (Set.Icc vLow vHigh) + eta.real (Set.Icc vLow vHigh)ᶜ =
          eta.real Set.univ :=
        MeasureTheory.measureReal_add_measureReal_compl measurableSet_Icc
      _ = 1 := MeasureTheory.probReal_univ
  have hmass_single : 1 - tol < eta.real (Set.Icc vLow vHigh) := by
    linarith
  have hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < eta.real (Set.Icc vLow vHigh) :=
    Filter.Eventually.of_forall (fun _ _ => hmass_single)
  rcases exists_theorem4_global_coalition_nonLow_endpoint_of_longTailed
      Mseq Iseq Kseq selected coalitionEmbedding globalCutoff noiseLaw eta hlong
      outcomeLaw globalChoice globalScore localCoordinates htol_pos
      htotalSupply_lt_one hmass hv houtcome_finite
      hchoice_mass_eq_aggregateDemand hcapacity_sum hlocalCoordinates_measurable
      hlocalCoordinates_map hcoalition_score
      hunmatched_iff_no_global_affordance with
    ⟨sigma, valueFloor, epsilon, hsigma_pos, hvalueFloor_lt,
      hepsilon_pos, hepsilon_le_one, hlarge, hmass', hclose⟩
  exact ⟨vLow, vHigh, sigma, valueFloor, epsilon, hv, hsigma_pos,
    hvalueFloor_lt, hepsilon_pos, hepsilon_le_one, hsmall, hlarge, hmass', hclose⟩

end

end PG24NoisyMatchingMarkets
