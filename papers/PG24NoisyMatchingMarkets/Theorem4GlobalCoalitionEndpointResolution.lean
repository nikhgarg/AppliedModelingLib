import PG24NoisyMatchingMarkets.Theorem4GlobalCoalitionSourceSemantics
import Mathlib.Tactic

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

theorem theorem4_nonLow_endpoint_of_local_cutoff_count
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {Admissible : ℕ → Type u}
    (localCutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh)
    (hlow_count :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (lowCutoffIndexSet (localCutoff C a)
            (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
              epsilonFloorSplitIndex (tol / 2) C) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1)))
              (nonLowCutoffIndexSet (localCutoff C a)
                (vHigh + theorem4HighTailQuantile noiseLaw sigma C)) tol) ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C,
            1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ a : Admissible C, ∀ value ∈ Set.Icc vLow vHigh,
            |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet (localCutoff C a)
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
                value (localCutoff C a) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet (localCutoff C a)
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
                vLow (localCutoff C a)| < tol) := by
  rcases exists_positive_epsilon_le_one_of_exp_error_lt htol_pos hsigma_pos with
    ⟨epsilon, hepsilon_pos, hepsilon_le_one, herror_lt⟩
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C a => nonLowCutoffIndexSet (localCutoff C a)
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C)
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
            (largeSubset C a) tol := by
    filter_upwards [hlow_count] with C hcountC a
    exact coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
      htol_pos (hcountC a)
  have hfloor_tail :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards
        [theorem4HighTailQuantile_upperTailMass_le_eventually noiseLaw hsigma_pos]
      with C htailC
    simpa only [add_sub_cancel_left] using htailC
  have hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (localCutoff C a c - vHigh) ≤ sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hfloor_tail] with C htailC a c hc
    exact le_trans
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right
          (floor_le_of_mem_nonLowCutoffIndexSet hc) vHigh))
      htailC
  have hdiff :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          independentAffordanceProbability
              (largeSubset C a)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (localCutoff C a c - vHigh)) -
            independentAffordanceProbability
              (largeSubset C a)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (localCutoff C a c - vLow)) ≤
              1 - Real.exp (-(2 * epsilon * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      noiseLaw hlong hv hepsilon_pos hepsilon_le_one hsigma_pos.le
      hhigh_le_sigma_div
  have hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vHigh (localCutoff C a) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vLow (localCutoff C a) < tol := by
    filter_upwards [hdiff] with C hdiffC a
    have hbridge_high :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vHigh (localCutoff C a)
    have hbridge_low :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vLow (localCutoff C a)
    exact lt_of_le_of_lt
      (by simpa [hbridge_high, hbridge_low] using hdiffC a) herror_lt
  have hwitness :=
    theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
      (noiseLaw := noiseLaw)
      (coalition := fun C : ℕ => fun _ : Admissible C =>
        (Finset.univ : Finset (Fin (C + 1))))
      (largeSubset := largeSubset) (cutoff := localCutoff)
      (valueMass := valueMass) (epsilon := tol)
      (vLow := fun _ : ℕ => fun _ : Admissible _ => vLow)
      (vHigh := fun _ : ℕ => fun _ : Admissible _ => vHigh)
      hlarge hmass hgap
  refine ⟨epsilon, hepsilon_pos, hepsilon_le_one, ?_⟩
  simpa [largeSubset] using
    (theorem4_coalitionAmplificationUniformWitness_source_clauses hwitness)

theorem exists_theorem4_global_coalition_nonLow_endpoint_of_longTailed
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
    {totalSupply tol vLow vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < eta.real (Set.Icc vLow vHigh))
    (hv : vLow < vHigh)
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
    ∃ sigma valueFloor epsilon : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
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
  rcases eventually_theorem4_global_coalition_low_cutoff_count_of_source_demand_semantics
      Mseq Iseq Kseq selected coalitionEmbedding globalCutoff noiseLaw eta hlong
      outcomeLaw globalChoice globalScore localCoordinates htol_pos htotalSupply_lt_one
      houtcome_finite hchoice_mass_eq_aggregateDemand hcapacity_sum
      hlocalCoordinates_measurable hlocalCoordinates_map
      hcoalition_score hunmatched_iff_no_global_affordance with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hlow_count⟩
  let localCutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a => coalitionCutoffRestriction (coalitionEmbedding C a) (globalCutoff C)
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
  have hlow_count' :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (lowCutoffIndexSet (localCutoff C a)
            (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card ≤
              epsilonFloorSplitIndex (tol / 2) C := by
    simpa [localCutoff] using hlow_count
  rcases theorem4_nonLow_endpoint_of_local_cutoff_count
      noiseLaw hlong localCutoff htol_pos hsigma_pos hmass hv hlow_count' with
    ⟨epsilon, hepsilon_pos, hepsilon_le_one, hendpoint⟩
  refine ⟨sigma, valueFloor, epsilon, hsigma_pos, hvalueFloor_lt,
    hepsilon_pos, hepsilon_le_one, ?_⟩
  simpa [localCutoff] using hendpoint

end

end PG24NoisyMatchingMarkets
