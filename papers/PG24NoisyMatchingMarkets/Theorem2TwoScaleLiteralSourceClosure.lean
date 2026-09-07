import PG24NoisyMatchingMarkets.Theorem2TwoScaleFailureRatioBridge
import PG24NoisyMatchingMarkets.Theorem4LiteralSourceStableAdapter

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/-- The semantic large block: exactly the local colleges not below the capacity floor. -/
noncomputable def theorem2LiteralLargeCutoffBlock
    {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply : ℝ}
    [IsProbabilityMeasure noiseLaw]
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Outcome : Type v} [MeasurableSpace Outcome]
    {GlobalCollege : Type w} [Fintype GlobalCollege]
    {Cutoff : Type x}
    (data : PG24LiteralSourceStableData C noiseLaw eta totalSupply
      StudentType Outcome GlobalCollege Cutoff)
    (vHigh sigma : ℝ) : Finset (Fin (C + 1)) :=
  nonLowCutoffIndexSet data.toExtendedCoalitionSourceStableInstance.localCutoff
    (vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
The capacity contradiction gives a semantic large block directly from literal
finite-preference demand, with no ordering of college labels.
-/
theorem theorem2_literalSource_exists_sigma_nonLowCutoffGeometry_of_longTailed
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
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          (theorem2LiteralLargeCutoffBlock (data C) vHigh sigma) splitTol ∧
        ∀ c ∈ theorem2LiteralLargeCutoffBlock (data C) vHigh sigma,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
  rcases
      PG24ExtendedCoalitionSourceStableInstance.exists_eventually_theorem4_source_instance_low_cutoff_count_of_longTailed
        noiseLaw eta hlong hsplitTol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hcount⟩
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) ≤
          sigma / ((C + 1 : ℕ) : ℝ) :=
    theorem4HighTailQuantile_upperTailMass_le_eventually noiseLaw hsigma_pos
  refine ⟨sigma, hsigma_pos, ?_⟩
  filter_upwards [hcount, hquantile_tail] with C hcountC hquantileC
  let inst := (data C).toExtendedCoalitionSourceStableInstance
  let floor : ℝ := vHigh + theorem4HighTailQuantile noiseLaw sigma C
  let large := theorem2LiteralLargeCutoffBlock (data C) vHigh sigma
  have hcount_inst :
      (lowCutoffIndexSet inst.localCutoff floor).card ≤
        epsilonFloorSplitIndex (splitTol / 2) C := by
    simpa [inst, floor] using
      (hcountC (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C)
        (CutoffSeq C) inst)
  have hlarge :
      CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1))) large splitTol := by
    apply coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
      hsplitTol_pos
    simpa [large, floor, inst, theorem2LiteralLargeCutoffBlock] using hcount_inst
  refine ⟨hlarge, ?_⟩
  intro c hc
  have hfloor : floor ≤ inst.localCutoff c := by
    simpa [large, floor, inst, theorem2LiteralLargeCutoffBlock] using
      (floor_le_of_mem_nonLowCutoffIndexSet hc)
  calc
    AppliedModelingLib.Probability.upperTailMass noiseLaw (inst.localCutoff c - vHigh) ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw (floor - vHigh) :=
      AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right hfloor vHigh)
    _ = AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) := by
      congr 1
      dsimp [floor]
      ring
    _ ≤ sigma / ((C + 1 : ℕ) : ℝ) := hquantileC

/--
Literal-source two-scale closure.  The capacity scale is selected first; the
endpoint is selected only after that scale is fixed.
-/
theorem theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_of_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply splitTol endpointTol vLow vHigh : ℝ}
    (hsplitTol_pos : 0 < splitTol) (hendpointTol_pos : 0 < endpointTol)
    (htotalSupply_lt_one : totalSupply < 1) (hv : vLow < vHigh)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) :
    ∃ sigma r : ℝ, 0 < sigma ∧ 0 < r ∧ r ≤ 1 ∧
      1 - Real.exp (-(2 * r * sigma)) < endpointTol ∧
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          (theorem2LiteralLargeCutoffBlock (data C) vHigh sigma) splitTol ∧
        ∀ c ∈ theorem2LiteralLargeCutoffBlock (data C) vHigh sigma,
          Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh)) /
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vLow)) ∧
            0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) ∧
            1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) ≤ 1 := by
  rcases theorem2_literalSource_exists_sigma_nonLowCutoffGeometry_of_longTailed
      CutoffSeq noiseLaw eta hlong hsplitTol_pos htotalSupply_lt_one data with
    ⟨sigma, hsigma_pos, hgeometry⟩
  rcases theorem2_exists_endpoint_error_after_scale hendpointTol_pos hsigma_pos with
    ⟨r, hr_pos, hr_le_one, hgap⟩
  let large : ∀ C : ℕ, Unit → Finset (Fin (C + 1)) :=
    fun C _ => theorem2LiteralLargeCutoffBlock (data C) vHigh sigma
  let cutoff : ∀ C : ℕ, Unit → Fin (C + 1) → ℝ :=
    fun C _ => (data C).toExtendedCoalitionSourceStableInstance.localCutoff
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
  have hcutoff_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Unit, ∀ c ∈ large C a, B ≤ cutoff C a c := by
    intro B
    have hquantile_ge :
        ∀ᶠ C : ℕ in atTop,
          B - vHigh ≤ theorem4HighTailQuantile noiseLaw sigma C :=
      hquantile_atTop
        (Filter.eventually_atTop.2 ⟨B - vHigh, fun z hz => hz⟩)
    filter_upwards [hquantile_ge] with C hquantileC a c hc
    have hfloor :
        vHigh + theorem4HighTailQuantile noiseLaw sigma C ≤ cutoff C a c := by
      simpa [large, cutoff, theorem2LiteralLargeCutoffBlock] using
        (floor_le_of_mem_nonLowCutoffIndexSet hc)
    linarith
  have hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Unit, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hgeometry] with C hgeometryC a c hc
    simpa [large, cutoff] using hgeometryC.2 c hc
  have hratio :=
    theorem2_eventually_largeFailureRatio_of_longTailed_unboundedCutoffGeometry
      (Admissible := fun _ : ℕ => Unit)
      (large := large) (cutoff := cutoff)
      noiseLaw hlong hv hr_pos hr_le_one hsigma_pos.le hcutoff_atTop
      hhigh_le_sigma_div
  refine ⟨sigma, r, hsigma_pos, hr_pos, hr_le_one, hgap, ?_⟩
  filter_upwards [hgeometry, hratio] with C hgeometryC hratioC
  refine ⟨hgeometryC.1, ?_⟩
  intro c hc
  simpa [large, cutoff] using hratioC Unit.unit c hc

end

end PG24NoisyMatchingMarkets
