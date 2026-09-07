import PG24NoisyMatchingMarkets.Theorem2TwoScaleRegionalSmallBridge

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/--
The small-block affordability estimate obtained from a source-derived regional
capacity inequality and the paper's split/cardinality capacity regularity.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_of_regional_capacity_regular
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small : Finset (Fin n)) (capacity : Fin n -> ℝ)
    {totalSupply alpha delta endpoint sigma vStar : ℝ} (cutoff : Fin n -> ℝ)
    (hregional_capacity :
      Real.sqrt delta *
          theorem2_twoScaleDenominator totalSupply delta endpoint sigma *
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin n => noiseLaw))
              small vStar cutoff ≤
        activeCapacity small capacity)
    (hcard : (small.card : ℝ) ≤ delta * (n : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hn_pos : 0 < (n : ℝ))
    (hcapacity : ∀ c ∈ small, capacity c ≤ alpha / (n : ℝ))
    (hdelta_pos : 0 < delta)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        small vStar cutoff) := by
  apply theorem2_twoScaleSmallFirmSourceBound_of_capacity_mass hdelta_pos hden_pos
  exact theorem2_twoScale_capacity_mass_le_delta_mul_alpha
    small capacity hcard halpha_nonneg hn_pos hcapacity hregional_capacity

/--
The source-model small-block bound, with the regional residual constructed
from global clearing and iid failure ratios and capacity regularity stated in
the paper's own form.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_of_sourceModel_regional_capacityRegular
    {StudentType : Type u} {n : ℕ} [MeasurableSpace StudentType]
    (studentLaw : Measure StudentType) [IsProbabilityMeasure studentLaw]
    (value : StudentType -> ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {largeRegion smallRegion : Set ℝ}
    {totalSupply alpha delta endpoint sigma vLow vHigh vStar : ℝ}
    (cutoff : Fin n -> ℝ)
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ valueLaw.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ valueLaw.real smallRegion)
    (hsmallRegion_ge : ∀ w : ℝ, w ∈ smallRegion -> vStar ≤ w)
    (hsmallRegion_le_high : ∀ w : ℝ, w ∈ smallRegion -> w ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hn_pos : 0 < (n : ℝ))
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / (n : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vLow) ≤ 1)
    (demand : StudentType × (Fin n -> ℝ) -> Option (Fin n))
    (hdemand_none_iff_no_crossed :
      ∀ outcome : StudentType × (Fin n -> ℝ),
        demand outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin n))
            (noisyScore (value outcome.1) outcome.2) cutoff)
    (hchosen_feasible :
      ∀ (outcome : StudentType × (Fin n -> ℝ)) (college : Fin n),
        demand outcome = some college ->
          cutoff college < value outcome.1 + outcome.2 college)
    (aggregateDemand capacity : Fin n -> ℝ)
    (hglobal_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand (Finset.univ : Finset (Fin n)) =
          ∑ c ∈ (Finset.univ : Finset (Fin n)), aggregateDemand c)
    (hsmall_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand small = ∑ c ∈ small, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply)
    (hsmall_card : (small.card : ℝ) ≤ delta * (n : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_regular : capacityRegular capacity alpha n)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small vStar cutoff) := by
  apply theorem2_twoScaleSmallFirmSourceBound_of_regional_capacity_regular
    noiseLaw small capacity cutoff
  · exact
      theorem2_twoScale_sourceModel_regional_smallFirm_capacity_lower_bound_of_global_largeResidual
        studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
        hdisjoint hcover cutoff hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge
        hsmallRegion_meas hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high
        hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
        hendpoint_nonneg hsigma_nonneg hn_pos hfailure_ratio hlow_failure_pos
        hlow_failure_le_one demand hdemand_none_iff_no_crossed hchosen_feasible
        aggregateDemand capacity hglobal_choice_mass hsmall_choice_mass hclearing
        htotal_capacity
  · exact hsmall_card
  · exact halpha_nonneg
  · exact hn_pos
  · intro c hc
    exact capacityRegular.le hcapacity_regular c
  · exact hdelta_pos
  · exact hden_pos

/-- A small-block source bound at `vStar` applies to every lower value. -/
theorem theorem2_twoScaleSmallFirmSourceBound_at_or_below_vStar
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small : Finset (Fin n)) {totalSupply alpha delta endpoint sigma v vStar : ℝ}
    (cutoff : Fin n -> ℝ) (hv : v ≤ vStar)
    (hbound : theorem2_twoScaleSmallFirmSourceBound
      totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small vStar cutoff)) :
    theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small v cutoff) := by
  unfold theorem2_twoScaleSmallFirmSourceBound at hbound ⊢
  exact (cutoffAffordanceProbability_mono_value
    (Measure.pi (fun _ : Fin n => noiseLaw)) hv).trans hbound

end

end PG24NoisyMatchingMarkets
