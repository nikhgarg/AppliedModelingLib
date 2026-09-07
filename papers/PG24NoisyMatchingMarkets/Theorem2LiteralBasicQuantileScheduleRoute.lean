import PG24NoisyMatchingMarkets.Theorem2LiteralBasicAmplificationRoute
import PG24NoisyMatchingMarkets.Theorem2QuantileSchedule

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

namespace PG24LiteralBasicTwoScaleInstance

/--
Holder regularity constructs the source value regions used by the literal
two-scale route.  The remaining eventual input is only the semantic cutoff
geometry and long-tail failure-ratio comparison for the resulting quantiles.
-/
theorem theorem2_exists_eventually_literalBasicRegularWindow_of_holder_interior
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    (CutoffSeq : ℕ → Type v)
    {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (hregular : PG24HolderIntervalRegular eta)
    (delta endpoint sigma : ℕ → ℝ)
    (hdelta_pos : ∀ C : ℕ, 0 < delta C)
    (hquantile_target_lt_one :
      ∀ C : ℕ, Real.sqrt (delta C) + delta C / 2 < 1)
    (hdelta_zero : Tendsto delta atTop (nhds 0))
    {v : ℝ}
    (hv_lower : 0 < eta.real (Set.Iio v))
    (hv_upper : 0 < eta.real (Set.Ioi v))
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (halpha_nonneg : 0 ≤ alpha)
    (hparameters :
      ∀ᶠ C : ℕ in atTop,
        totalSupply + delta C < 1 ∧
        0 ≤ theorem2_twoScaleDenominator totalSupply (delta C)
          (endpoint C) (sigma C) ∧
        0 ≤ endpoint C ∧
        0 ≤ sigma C ∧
        0 < theorem2_twoScaleDenominator totalSupply (delta C)
          (endpoint C) (sigma C))
    (hgeometry_failure :
      ∀ vLow vHigh vStar : ℕ → ℝ,
        (∀ C : ℕ,
          Theorem2ExactQuantileWindow eta (delta C)
            (vLow C) (vHigh C) (vStar C)) →
        ∀ᶠ C : ℕ in atTop,
          CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
            (theorem2LiteralLargeCutoffBlock (inst C).literal
              (vHigh C) (sigma C)) (delta C) ∧
          ∀ c ∈ theorem2LiteralLargeCutoffBlock (inst C).literal
              (vHigh C) (sigma C),
            Real.exp (-(2 * endpoint C * sigma C / ((C + 1 : ℕ) : ℝ))) ≤
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                    vHigh C)) /
                  (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                    ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                      vLow C)) ∧
              0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                  vLow C) ∧
              1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C).literal.toExtendedCoalitionSourceStableInstance.localCutoff c -
                  vLow C) ≤ 1) :
    ∃ vLow vHigh vStar : ℕ → ℝ,
      (∀ C : ℕ,
        Theorem2ExactQuantileWindow eta (delta C)
          (vLow C) (vHigh C) (vStar C)) ∧
      ∀ᶠ C : ℕ in atTop,
        theorem2TwoScaleRegularWindow totalSupply alpha (delta C)
          (endpoint C) (sigma C)
          (cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (inst C).selectedCutoffVector) := by
  rcases theorem2_exists_interiorQuantileSchedule_of_holder
      eta hregular delta hdelta_pos hquantile_target_lt_one hdelta_zero
      hv_lower hv_upper with
    ⟨vLow, vHigh, vStar, hwindow, hmember⟩
  refine ⟨vLow, vHigh, vStar, hwindow, ?_⟩
  have hfailure := hgeometry_failure vLow vHigh vStar hwindow
  filter_upwards [hmember, hparameters, hfailure] with C hmemberC hparametersC
      hfailureC
  rcases hparametersC with
    ⟨htotalSupply_delta_lt_one, hdenom_nonneg, hendpoint_nonneg,
      hsigma_nonneg, hden_pos⟩
  rcases (hwindow C).valueRegions with
    ⟨hlarge_meas, hlarge_mass, hlarge_ge, hlarge_le_high, hsmall_meas,
      hsmall_mass, hsmall_ge, hsmall_le_high⟩
  rcases hmemberC with ⟨hv_low, hv_high, hv_star⟩
  refine theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
    (inst C) hfailureC.1 hlarge_meas hlarge_mass hlarge_ge hlarge_le_high
    hsmall_meas hsmall_mass hsmall_ge hsmall_le_high
    (hdelta_pos C) htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
    hendpoint_nonneg hsigma_nonneg hv_low hv_high hv_star ?_ ?_ ?_
    halpha_nonneg hden_pos
  · intro c hc
    exact (hfailureC.2 c hc).1
  · intro c hc
    exact (hfailureC.2 c hc).2.1
  · intro c hc
    exact (hfailureC.2 c hc).2.2

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
