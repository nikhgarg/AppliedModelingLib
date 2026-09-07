import PG24NoisyMatchingMarkets.Theorem2LiteralBasicRegularWindow
import PG24NoisyMatchingMarkets.Theorem2TwoScaleLiteralSourceClosure

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

namespace PG24LiteralBasicTwoScaleInstance

variable {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Cutoff : Type v}

/--
The semantic low/non-low cutoff split closes the fixed-`C` literal route once
the long-tail comparison is available on the non-low block.
-/
theorem theorem2_twoScaleRegularWindow_of_literalBasic_nonLowFailureRatio
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    {floor delta endpoint sigma vLow vHigh vStar v : ℝ}
    (hlarge :
      CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
        (nonLowCutoffIndexSet inst.selectedCutoffVector floor) delta)
    {largeRegion smallRegion : Set ℝ}
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ eta.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hlargeRegion_le_high : ∀ w : ℝ, w ∈ largeRegion -> w ≤ vHigh)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ eta.real smallRegion)
    (hsmallRegion_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hsmallRegion_le_high : ∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
    (hfailure_ratio :
      ∀ c ∈ nonLowCutoffIndexSet inst.selectedCutoffVector floor,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (inst.selectedCutoffVector c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (inst.selectedCutoffVector c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ nonLowCutoffIndexSet inst.selectedCutoffVector floor,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ nonLowCutoffIndexSet inst.selectedCutoffVector floor,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow) ≤ 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) v inst.selectedCutoffVector) := by
  let small := lowCutoffIndexSet inst.selectedCutoffVector floor
  let large := nonLowCutoffIndexSet inst.selectedCutoffVector floor
  have hsmall_subset : small ⊆ (Finset.univ : Finset (Fin (C + 1))) := by
    intro c _hc
    simp
  have hdisjoint : Disjoint small large := by
    simpa [small, large, nonLowCutoffIndexSet] using
      (Finset.disjoint_sdiff : Disjoint small ((Finset.univ : Finset (Fin (C + 1))) \ small))
  have hcover : small ∪ large = (Finset.univ : Finset (Fin (C + 1))) := by
    simpa [small, large, nonLowCutoffIndexSet] using
      (Finset.union_sdiff_of_subset hsmall_subset)
  have hsmall_card : (small.card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ) := by
    simpa [small, large] using
      (lowCutoffIndexSet_card_le_of_coalitionLargeSubset_nonLow hlarge)
  exact theorem2_twoScaleRegularWindow_of_literalBasic_checked_bounds
    inst small large hdisjoint hcover
    hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hlargeRegion_le_high
    hsmallRegion_meas hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high
    hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
    hendpoint_nonneg hsigma_nonneg hv_low hv_high hv_star
    (by simpa [large] using hfailure_ratio)
    (by simpa [large] using hlow_failure_pos)
    (by simpa [large] using hlow_failure_le_one)
    hsmall_card halpha_nonneg hden_pos

/--
The literal-source non-low block and failure ratio feed the fixed-`C` route
after the canonical-coordinate equality is proved from the basic instance.
-/
theorem theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    {delta endpoint sigma vLow vHigh vStar v : ℝ}
    (hlarge :
      CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
        (theorem2LiteralLargeCutoffBlock inst.literal vHigh sigma) delta)
    {largeRegion smallRegion : Set ℝ}
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ eta.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hlargeRegion_le_high : ∀ w : ℝ, w ∈ largeRegion -> w ≤ vHigh)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ eta.real smallRegion)
    (hsmallRegion_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hsmallRegion_le_high : ∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
    (hfailure_ratio :
      ∀ c ∈ theorem2LiteralLargeCutoffBlock inst.literal vHigh sigma,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (inst.literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (inst.literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ theorem2LiteralLargeCutoffBlock inst.literal vHigh sigma,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ theorem2LiteralLargeCutoffBlock inst.literal vHigh sigma,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) ≤ 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) v inst.selectedCutoffVector) := by
  let floor : ℝ := vHigh + theorem4HighTailQuantile noiseLaw sigma C
  have hlarge' :
      CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
        (nonLowCutoffIndexSet inst.selectedCutoffVector floor) delta := by
    rw [inst.selectedCutoffVector_eq_localCutoff]
    simpa [floor, theorem2LiteralLargeCutoffBlock] using hlarge
  apply theorem2_twoScaleRegularWindow_of_literalBasic_nonLowFailureRatio
    inst hlarge'
    hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hlargeRegion_le_high
    hsmallRegion_meas hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high
    hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
    hendpoint_nonneg hsigma_nonneg hv_low hv_high hv_star
  · intro c hc
    rw [inst.selectedCutoffVector_eq_localCutoff]
    rw [inst.selectedCutoffVector_eq_localCutoff] at hc
    apply hfailure_ratio c
    simpa [floor, theorem2LiteralLargeCutoffBlock] using hc
  · intro c hc
    rw [inst.selectedCutoffVector_eq_localCutoff]
    rw [inst.selectedCutoffVector_eq_localCutoff] at hc
    apply hlow_failure_pos c
    simpa [floor, theorem2LiteralLargeCutoffBlock] using hc
  · intro c hc
    rw [inst.selectedCutoffVector_eq_localCutoff]
    rw [inst.selectedCutoffVector_eq_localCutoff] at hc
    apply hlow_failure_le_one c
    simpa [floor, theorem2LiteralLargeCutoffBlock] using hc
  · exact halpha_nonneg
  · exact hden_pos

/--
Eventual fixed-target assembly for literal basic instances.  The value regions
are retained as explicit source obligations; this theorem deliberately makes
no claim that a single eta schedule covers every real target.
-/
theorem theorem2_eventually_literalBasicRegularWindow_of_explicit_valueRegions
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    (CutoffSeq : ℕ → Type v)
    {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    {delta endpoint sigma vLow vHigh vStar v : ℝ}
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
    (halpha_nonneg : 0 ≤ alpha)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hvalueRegions :
      ∀ᶠ C : ℕ in atTop,
        ∃ largeRegion smallRegion : Set ℝ,
          MeasurableSet largeRegion ∧
          1 - delta ≤ eta.real largeRegion ∧
          (∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w) ∧
          (∀ w : ℝ, w ∈ largeRegion -> w ≤ vHigh) ∧
          MeasurableSet smallRegion ∧
          Real.sqrt delta ≤ eta.real smallRegion ∧
          (∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w) ∧
          (∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh))
    (hfailure :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          (theorem2LiteralLargeCutoffBlock (inst C).literal vHigh sigma) delta ∧
        ∀ c ∈ theorem2LiteralLargeCutoffBlock (inst C).literal vHigh sigma,
          Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh)) /
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow)) ∧
            0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) ∧
            1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) ≤ 1) :
    ∀ᶠ C : ℕ in atTop,
      theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
        (cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v
          (inst C).selectedCutoffVector) := by
  filter_upwards [hvalueRegions, hfailure] with C hregionsC hfailureC
  rcases hregionsC with
    ⟨largeRegion, smallRegion, hlarge_meas, hlarge_mass, hlarge_ge,
      hlarge_le_high, hsmall_meas, hsmall_mass, hsmall_ge, hsmall_le_high⟩
  refine theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
    (inst C) hfailureC.1 hlarge_meas hlarge_mass hlarge_ge hlarge_le_high
    hsmall_meas hsmall_mass hsmall_ge hsmall_le_high
    hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
    hendpoint_nonneg hsigma_nonneg hv_low hv_high hv_star ?_ ?_ ?_
    halpha_nonneg hden_pos
  · intro c hc
    exact (hfailureC.2 c hc).1
  · intro c hc
    exact (hfailureC.2 c hc).2.1
  · intro c hc
    exact (hfailureC.2 c hc).2.2

/--
The small-region part of the local two-scale proof cannot cover a target above
the eta support: it would require positive eta mass at values at least that
target.  Thus long-tail cutoff geometry alone cannot repair all-real coverage.
-/
theorem theorem2_no_smallValueRegion_above_eta_support
    (eta : Measure ℝ) [IsFiniteMeasure eta]
    {delta v vStar : ℝ} {smallRegion : Set ℝ}
    (hdelta_pos : 0 < delta)
    (hv_star : v ≤ vStar)
    (hsmall_mass : Real.sqrt delta ≤ eta.real smallRegion)
    (hsmall_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hno_high_mass : eta.real (Set.Ici v) = 0) :
    False := by
  have hsubset : smallRegion ⊆ Set.Ici v := by
    intro w hw
    exact le_trans hv_star (hsmall_ge w hw)
  have hsmall_le : eta.real smallRegion ≤ eta.real (Set.Ici v) :=
    MeasureTheory.measureReal_mono hsubset (measure_ne_top eta _)
  have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta_pos
  rw [hno_high_mass] at hsmall_le
  linarith

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
