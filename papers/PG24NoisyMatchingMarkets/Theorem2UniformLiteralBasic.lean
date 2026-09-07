import PG24NoisyMatchingMarkets.Theorem2FixedTargetLiteralBasic

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w

namespace PG24LiteralBasicTwoScaleInstance

/--
The literal-source cutoff construction with its arbitrary-instance quantifier
preserved.  The scale and endpoint are fixed before the admissible source
instance is supplied, matching the source theorem's stable-matching
uniformity.
-/
theorem theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_uniform_of_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {Admissible : ℕ → Type v} (CutoffSeq : ℕ → Type w)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply alpha splitTol endpointTol vLow vHigh : ℝ}
    (hsplitTol_pos : 0 < splitTol) (hendpointTol_pos : 0 < endpointTol)
    (htotalSupply_lt_one : totalSupply < 1) (hv : vLow < vHigh)
    (inst : ∀ C : ℕ, Admissible C →
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C)) :
    ∃ sigma endpoint : ℝ, 0 < sigma ∧ 0 < endpoint ∧ endpoint ≤ 1 ∧
      1 - Real.exp (-(2 * endpoint * sigma)) < endpointTol ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
            (theorem2LiteralLargeCutoffBlock (inst C a).literal vHigh sigma) splitTol ∧
          ∀ c ∈ theorem2LiteralLargeCutoffBlock (inst C a).literal vHigh sigma,
            Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((inst C a).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                    vHigh)) /
                  (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                    ((inst C a).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                      vLow)) ∧
              0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C a).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                  vLow) ∧
              1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C a).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                  vLow) ≤ 1 := by
  rcases
      PG24ExtendedCoalitionSourceStableInstance.exists_eventually_theorem4_source_instance_low_cutoff_count_of_longTailed
        noiseLaw eta hlong hsplitTol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hcount⟩
  rcases theorem2_exists_endpoint_error_after_scale hendpointTol_pos hsigma_pos with
    ⟨endpoint, hendpoint_pos, hendpoint_le_one, hgap⟩
  let large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C a => theorem2LiteralLargeCutoffBlock (inst C a).literal vHigh sigma
  let cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a => (inst C a).literal.toExtendedCoalitionSourceStableInstance.localCutoff
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) ≤
          sigma / ((C + 1 : ℕ) : ℝ) :=
    theorem4HighTailQuantile_upperTailMass_le_eventually noiseLaw hsigma_pos
  have hgeometry :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
            (large C a) splitTol ∧
          ∀ c ∈ large C a,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C a c - vHigh) ≤
              sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcount, hquantile_tail] with C hcountC hquantileC a
    let sourceInst := (inst C a).literal.toExtendedCoalitionSourceStableInstance
    let floor : ℝ := vHigh + theorem4HighTailQuantile noiseLaw sigma C
    have hcountInst :
        (lowCutoffIndexSet sourceInst.localCutoff floor).card ≤
          epsilonFloorSplitIndex (splitTol / 2) C := by
      simpa [sourceInst, floor] using
        (hcountC (StudentTypeSeq C)
          (StudentTypeSeq C × (Fin (C + 1) → ℝ))
          (Fin (C + 1)) (CutoffSeq C) sourceInst)
    have hlarge :
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          (large C a) splitTol := by
      apply coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
        hsplitTol_pos
      simpa [large, sourceInst, floor, theorem2LiteralLargeCutoffBlock] using hcountInst
    refine ⟨hlarge, ?_⟩
    intro c hc
    have hfloor : floor ≤ sourceInst.localCutoff c := by
      simpa [large, sourceInst, floor, theorem2LiteralLargeCutoffBlock] using
        (floor_le_of_mem_nonLowCutoffIndexSet hc)
    calc
      AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff C a c - vHigh) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw (floor - vHigh) :=
        AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (by simpa [cutoff, sourceInst] using hfloor) vHigh)
      _ = AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) := by
        congr 1
        dsimp [floor]
        ring
      _ ≤ sigma / ((C + 1 : ℕ) : ℝ) := hquantileC
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
      hbound_zero hquantile_tail
  have hcutoff_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a, B ≤ cutoff C a c := by
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
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hgeometry] with C hgeometryC a c hc
    exact (hgeometryC a).2 c hc
  have hratio :=
    theorem2_eventually_largeFailureRatio_of_longTailed_unboundedCutoffGeometry
      (Admissible := Admissible) (large := large) (cutoff := cutoff)
      noiseLaw hlong hv hendpoint_pos hendpoint_le_one hsigma_pos.le
      hcutoff_atTop hhigh_le_sigma_div
  refine ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one, hgap, ?_⟩
  filter_upwards [hgeometry, hratio] with C hgeometryC hratioC a
  refine ⟨(hgeometryC a).1, ?_⟩
  intro c hc
  simpa [large, cutoff] using hratioC a c hc

/--
For one fixed support-interior target and tolerance, the literal basic-model
two-scale window holds eventually for every admissible selected instance.  All
parameters are chosen before the per-market instance quantifier.
-/
theorem theorem2_exists_eventually_fixedTargetRegularWindow_uniform_of_holder_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {Admissible : ℕ → Type v} (CutoffSeq : ℕ → Type w)
    {noiseLaw eta : Measure ℝ} {totalSupply alpha target tol : ℝ}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : ∀ C : ℕ, Admissible C →
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (hregular : PG24HolderIntervalRegular eta)
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (htarget_lower : 0 < eta.real (Set.Iio target))
    (htarget_upper : 0 < eta.real (Set.Ioi target))
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol) :
    ∃ delta sigma endpoint vLow vHigh vStar : ℝ,
      Theorem2ExactQuantileWindow eta delta vLow vHigh vStar ∧
      theorem2_localWindowMembership vLow vHigh vStar target ∧
      0 < delta ∧
      totalSupply + delta < 1 ∧
      0 < sigma ∧ 0 < endpoint ∧ endpoint ≤ 1 ∧
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
      theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
      theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
            (cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) target
              (inst C a).selectedCutoffVector) := by
  letI : NoAtoms eta := hregular.noAtoms
  rcases theorem2_exists_split_gap_budget_for_fixed_tolerance_at_interior_target
      htotalSupply_lt_one halpha_nonneg htol_pos htarget_lower htarget_upper with
    ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
      hbudget_den_pos, hlower_budget, hupper_budget, htarget_lower_budget,
      htarget_upper_budget, htransfer⟩
  rcases theorem2_exists_exactQuantileWindow_of_noAtoms
      eta hdelta_pos hquantile with
    ⟨vLow, vHigh, vStar, hwindow⟩
  have hmember : theorem2_localWindowMembership vLow vHigh vStar target :=
    theorem2_localWindowMembership_of_exactQuantileWindow_of_interiorBudgets
      eta hwindow htarget_lower_budget htarget_upper_budget
  rcases
      theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_uniform_of_longTailed
        CutoffSeq noiseLaw eta hlong hdelta_pos hgap_pos htotalSupply_lt_one
        hwindow.lower_lt_upper inst with
    ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one, hgap,
      hfailure⟩
  rcases htransfer endpoint sigma hgap with ⟨hden_pos, hlower, hupper⟩
  refine ⟨delta, sigma, endpoint, vLow, vHigh, vStar, hwindow, hmember,
    hdelta_pos, hsupply_split, hsigma_pos, hendpoint_pos, hendpoint_le_one,
    hden_pos, hlower, hupper, ?_⟩
  rcases hwindow.valueRegions with
    ⟨hlarge_meas, hlarge_mass, hlarge_ge, hlarge_le_high, hsmall_meas,
      hsmall_mass, hsmall_ge, hsmall_le_high⟩
  filter_upwards [hfailure] with C hfailureC a
  refine theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
    (inst C a) (hfailureC a).1 hlarge_meas hlarge_mass hlarge_ge hlarge_le_high
    hsmall_meas hsmall_mass hsmall_ge hsmall_le_high
    hdelta_pos htotalSupply_pos.le hsupply_split hden_pos.le
    hendpoint_pos.le hsigma_pos.le hmember.1 hmember.2.1 hmember.2.2 ?_ ?_ ?_
    halpha_nonneg hden_pos
  · intro c hc
    exact ((hfailureC a).2 c hc).1
  · intro c hc
    exact ((hfailureC a).2 c hc).2.1
  · intro c hc
    exact ((hfailureC a).2 c hc).2.2

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
