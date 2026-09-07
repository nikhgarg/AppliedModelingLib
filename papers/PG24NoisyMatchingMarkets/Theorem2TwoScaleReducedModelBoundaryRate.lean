import PG24NoisyMatchingMarkets.Theorem4LiteralSourceStableAdapter

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
Intermediate reduced-model capacity geometry.  This deliberately stops before
any T2 source-native endpoint claim; that requires the literal-demand adapter.
-/
theorem theorem2_reducedModel_exists_sigma_suffix_geometry_of_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply splitTol vHigh : ℝ}
    (hsplitTol_pos : 0 < splitTol) (htotalSupply_lt_one : totalSupply < 1)
    (inst : ∀ C : ℕ,
      PG24ExtendedCoalitionSourceStableInstance C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C))
    (hsorted :
      ∀ᶠ C : ℕ in atTop,
        ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
          (inst C).localCutoff i ≤ (inst C).localCutoff j) :
    ∃ sigma : ℝ, 0 < sigma ∧
      (∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (splitTol / 2) C) C,
          B ≤ (inst C).localCutoff c) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (splitTol / 2) C) C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((inst C).localCutoff c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) := by
  rcases
      PG24ExtendedCoalitionSourceStableInstance.exists_eventually_theorem4_source_instance_low_cutoff_count_of_longTailed
        noiseLaw eta hlong hsplitTol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hcount⟩
  have hquantile_upper :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) ≤
          sigma / ((C + 1 : ℕ) : ℝ) :=
    theorem4HighTailQuantile_upperTailMass_le_eventually noiseLaw hsigma_pos
  have hden_tendsto :
      Tendsto (fun C : ℕ => ((C + 1 : ℕ) : ℝ)) atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_atTop
  have hbound_zero :
      Tendsto (fun C : ℕ => sigma / ((C + 1 : ℕ) : ℝ))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto sigma
  have hquantile_atTop :
      Tendsto (fun C : ℕ => theorem4HighTailQuantile noiseLaw sigma C)
        atTop atTop :=
    AppliedModelingLib.Probability.tendsto_atTop_of_upperTailMass_le_tendsto_zero
      noiseLaw
      (hlong.eventually_pos
        (fun z => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw z))
      hbound_zero hquantile_upper
  refine ⟨sigma, hsigma_pos, ?_, ?_⟩
  · intro B
    have hquantile_ge :
        ∀ᶠ C : ℕ in atTop,
          B - vHigh ≤ theorem4HighTailQuantile noiseLaw sigma C :=
      hquantile_atTop
        (Filter.eventually_atTop.2 ⟨B - vHigh, fun z hz => hz⟩)
    filter_upwards [hquantile_ge, hcount, hsorted] with
      C hquantileC hcountC hsortedC c hc
    have hfloor :
        vHigh + theorem4HighTailQuantile noiseLaw sigma C ≤
          (inst C).localCutoff c :=
      suffix_floor_of_sorted_lowCutoffIndexSet_card_le hsortedC
        (hcountC (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C)
          (CutoffSeq C) (inst C))
        (Finset.mem_filter.mp hc).2
    linarith
  · filter_upwards [hcount, hsorted, hquantile_upper] with
      C hcountC hsortedC hquantileC c hc
    have hfloor :
        vHigh + theorem4HighTailQuantile noiseLaw sigma C ≤
          (inst C).localCutoff c :=
      suffix_floor_of_sorted_lowCutoffIndexSet_card_le hsortedC
        (hcountC (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C)
          (CutoffSeq C) (inst C))
        (Finset.mem_filter.mp hc).2
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw (by
          linarith [hfloor]))
        hquantileC

/--
Literal finite-preference demand supplies the reduced-model capacity geometry.
The conclusion intentionally stops before a T2 endpoint or failure-ratio claim.
-/
theorem theorem2_literalSource_exists_sigma_suffix_geometry_of_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply splitTol vHigh : ℝ}
    (hsplitTol_pos : 0 < splitTol) (htotalSupply_lt_one : totalSupply < 1)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C))
    (hsorted :
      ∀ᶠ C : ℕ in atTop,
        ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
            ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      (∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (splitTol / 2) C) C,
          B ≤ (data C).toExtendedCoalitionSourceStableInstance.localCutoff c) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (splitTol / 2) C) C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) := by
  exact theorem2_reducedModel_exists_sigma_suffix_geometry_of_longTailed
    CutoffSeq noiseLaw eta hlong hsplitTol_pos htotalSupply_lt_one
    (fun C => (data C).toExtendedCoalitionSourceStableInstance) hsorted

end

end PG24NoisyMatchingMarkets
