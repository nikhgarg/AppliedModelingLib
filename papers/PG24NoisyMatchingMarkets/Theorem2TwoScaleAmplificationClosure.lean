import PG24NoisyMatchingMarkets.Theorem2TwoScaleLargeLowerBridge

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The explicit two-scale approximation window for one regular value. -/
def theorem2TwoScaleRegularWindow
    (totalSupply alpha delta r sigma p : ℝ) : Prop :=
  totalSupply - theorem2_twoScaleLowerError alpha delta r sigma ≤ p ∧
    p ≤ totalSupply + theorem2_twoScaleUpperError totalSupply alpha delta r sigma

/--
The lower large-block estimate transports from the high endpoint back through
the checked iid endpoint gap.  This is the lower half of
`proof-amplifying.tex:194-216`.
-/
theorem theorem2_twoScale_largeLower_of_high_lower_and_endpoint_gap
    {pLarge : ℝ -> ℝ}
    {totalSupply alpha delta r sigma vLow vHigh v : ℝ}
    (hp_mono : Monotone pLarge) (hv_low : vLow ≤ v)
    (hhigh_lower : totalSupply - (1 + alpha) * delta ≤ pLarge vHigh)
    (hendpoint_gap :
      pLarge vHigh - pLarge vLow ≤ theorem2_twoScaleProductGap r sigma) :
    totalSupply - theorem2_twoScaleLowerError alpha delta r sigma ≤ pLarge v := by
  have hlow_to_value : pLarge vLow ≤ pLarge v := hp_mono hv_low
  have hgap : pLarge vHigh - pLarge vLow ≤
      1 - Real.exp (-(2 * r * sigma)) := by
    simpa [theorem2_twoScaleProductGap] using hendpoint_gap
  unfold theorem2_twoScaleLowerError
  linarith

/-- The checked residual inequality is exactly the large-block upper bound. -/
theorem theorem2_twoScale_largeUpper_of_residual
    {totalSupply delta r sigma pLarge : ℝ}
    (hresidual :
      theorem2_twoScaleDenominator totalSupply delta r sigma ≤ 1 - pLarge) :
    pLarge ≤ totalSupply + delta + theorem2_twoScaleProductGap r sigma := by
  have hraw : pLarge ≤ totalSupply + delta +
      (1 - Real.exp (-(2 * r * sigma))) := by
    unfold theorem2_twoScaleDenominator at hresidual
    simp only [theorem2_twoScaleProductGap] at hresidual
    linarith
  simpa [theorem2_twoScaleProductGap] using hraw

/--
Scalar closure of the paper's small/large affordance decomposition.  Each
input is an inequality about an actual block probability; no local endpoint
or final-window package is used.
-/
theorem theorem2_twoScaleRegularWindow_of_block_bounds
    {totalSupply alpha delta r sigma pSmall pLarge pTotal : ℝ}
    (hlarge_le_total : pLarge ≤ pTotal)
    (htotal_le_blocks : pTotal ≤ pSmall + pLarge)
    (hlarge_lower :
      totalSupply - theorem2_twoScaleLowerError alpha delta r sigma ≤ pLarge)
    (hlarge_upper :
      pLarge ≤ totalSupply + delta + theorem2_twoScaleProductGap r sigma)
    (hsmall :
      theorem2_twoScaleSmallFirmSourceBound
        totalSupply alpha delta r sigma pSmall) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta r sigma pTotal := by
  constructor
  · exact hlarge_lower.trans hlarge_le_total
  · have hsmall' : pSmall ≤
        alpha * Real.sqrt delta /
          theorem2_twoScaleDenominator totalSupply delta r sigma := by
      simpa [theorem2_twoScaleSmallFirmSourceBound] using hsmall
    calc
      pTotal ≤ pSmall + pLarge := htotal_le_blocks
      _ ≤ alpha * Real.sqrt delta /
            theorem2_twoScaleDenominator totalSupply delta r sigma +
            (totalSupply + delta + theorem2_twoScaleProductGap r sigma) :=
        add_le_add hsmall' hlarge_upper
      _ = totalSupply +
            theorem2_twoScaleUpperError totalSupply alpha delta r sigma := by
        unfold theorem2_twoScaleUpperError theorem2_twoScaleDenominator
          theorem2_twoScaleProductGap
        ring

/--
The concrete cutoff-affordance closure on a regular interval.  This scalar
form consumes checked block bounds; the source-model closure below derives the
high-end large lower from demand, clearing, and capacity regularity.
-/
theorem theorem2_twoScaleCutoffRegularWindow_of_checked_block_bounds
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (small large : Finset (Fin n))
    (hcover : small ∪ large = (Finset.univ : Finset (Fin n)))
    {totalSupply alpha delta r sigma vLow vHigh v : ℝ}
    (cutoff : Fin n -> ℝ) (hv_low : vLow ≤ v)
    (hlarge_high_lower :
      totalSupply - (1 + alpha) * delta ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff)
    (hlarge_endpoint_gap :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
        theorem2_twoScaleProductGap r sigma)
    (hlarge_residual :
      theorem2_twoScaleDenominator totalSupply delta r sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff)
    (hsmall : theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta r sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small v cutoff)) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta r sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff) := by
  let productLaw : Measure (Fin n -> ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  haveI : IsProbabilityMeasure productLaw := by
    dsimp [productLaw]
    infer_instance
  let pLarge : ℝ -> ℝ :=
    fun w => cutoffAffordanceProbability productLaw large w cutoff
  have hlarge_lower :
      totalSupply - theorem2_twoScaleLowerError alpha delta r sigma ≤ pLarge v := by
    exact theorem2_twoScale_largeLower_of_high_lower_and_endpoint_gap
      (fun x y hxy => cutoffAffordanceProbability_mono_value productLaw hxy)
      hv_low (by simpa [pLarge, productLaw] using hlarge_high_lower)
      (by simpa [pLarge, productLaw] using hlarge_endpoint_gap)
  have hlarge_upper :
      pLarge v ≤ totalSupply + delta + theorem2_twoScaleProductGap r sigma := by
    exact theorem2_twoScale_largeUpper_of_residual
      (by simpa [pLarge, productLaw] using hlarge_residual)
  rcases cutoffAffordanceProbability_decomposition_of_union
      productLaw (total := Finset.univ) hcover.symm with
    ⟨hlarge_le_total, htotal_le_blocks⟩
  exact theorem2_twoScaleRegularWindow_of_block_bounds
    (by simpa [pLarge, productLaw] using hlarge_le_total)
    (by simpa [productLaw] using htotal_le_blocks)
    hlarge_lower hlarge_upper (by simpa [productLaw] using hsmall)

/--
The source-model closure for one regular value.  The large high-end lower is
derived from source demand and clearing; the remaining inputs are the iid
failure-ratio comparison and the two regular value regions.
-/
theorem theorem2_twoScaleCutoffRegularWindow_of_sourceModel_checked_bounds
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
    {totalSupply alpha delta endpoint sigma vLow vHigh vStar v : ℝ}
    (cutoff : Fin n -> ℝ)
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ valueLaw.real largeRegion)
    (hlargeRegion_ge : ∀ w : ℝ, w ∈ largeRegion -> vLow ≤ w)
    (hlargeRegion_le_high : ∀ w : ℝ, w ∈ largeRegion -> w ≤ vHigh)
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
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
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
    (hlarge_choice_mass :
      choiceMass
        (studentLaw.prod (Measure.pi (fun _ : Fin n => noiseLaw)))
        demand large = ∑ c ∈ large, aggregateDemand c)
    (hclearing : ∀ c : Fin n, aggregateDemand c = capacity c)
    (htotal_capacity : (∑ c : Fin n, capacity c) = totalSupply)
    (hsmall_card : (small.card : ℝ) ≤ delta * (n : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_regular : capacityRegular capacity alpha n)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw))
        (Finset.univ : Finset (Fin n)) v cutoff) := by
  have hlarge_high_lower :
      totalSupply - (1 + alpha) * delta ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff :=
    theorem2_sourceModel_largeHigh_lower_of_capacityRegular
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
      hdisjoint hcover cutoff hlargeRegion_meas hlargeRegion_mass
      hlargeRegion_le_high demand hchosen_feasible aggregateDemand capacity
      hlarge_choice_mass hclearing htotal_capacity hsmall_card halpha_nonneg
      hn_pos hcapacity_regular
  have hlarge_endpoint_gap :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vHigh cutoff -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large vLow cutoff ≤
        theorem2_twoScaleProductGap endpoint sigma :=
    theorem2_twoScale_iidLargeEndpointGap_of_failureRatio
      noiseLaw large cutoff hendpoint_nonneg hsigma_nonneg hn_pos
      hfailure_ratio hlow_failure_pos hlow_failure_le_one
  have hlarge_residual :
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) large v cutoff :=
    theorem2_twoScale_residual_of_sourceModel_globalClearing_and_failureRatio
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw large cutoff
      hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hdelta_pos
      htotalSupply_nonneg htotalSupply_delta_lt_one hv_high hendpoint_nonneg
      hsigma_nonneg hn_pos hfailure_ratio hlow_failure_pos hlow_failure_le_one
      demand hdemand_none_iff_no_crossed aggregateDemand capacity
      hglobal_choice_mass hclearing htotal_capacity
  have hsmall_at_star :
      theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
        (cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) small vStar cutoff) :=
    theorem2_twoScaleSmallFirmSourceBound_of_sourceModel_regional_capacityRegular
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
      hdisjoint hcover cutoff hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge
      hsmallRegion_meas hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high
      hdelta_pos htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
      hendpoint_nonneg hsigma_nonneg hn_pos hfailure_ratio hlow_failure_pos
      hlow_failure_le_one demand hdemand_none_iff_no_crossed hchosen_feasible
      aggregateDemand capacity hglobal_choice_mass hsmall_choice_mass hclearing
      htotal_capacity hsmall_card halpha_nonneg hcapacity_regular hden_pos
  have hsmall : theorem2_twoScaleSmallFirmSourceBound
      totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) small v cutoff) :=
    theorem2_twoScaleSmallFirmSourceBound_at_or_below_vStar
      noiseLaw small cutoff hv_star hsmall_at_star
  exact theorem2_twoScaleCutoffRegularWindow_of_checked_block_bounds
    noiseLaw small large hcover cutoff hv_low hlarge_high_lower
    hlarge_endpoint_gap hlarge_residual hsmall

/--
Once source semantics establish the explicit regular window eventually, the
two-stage schedule `delta`, then `r = delta / (1 + |sigma|)`, gives the
paper's uniform amplification conclusion.
-/
theorem theorem2_uniformAmplification_of_eventual_twoScaleRegularWindow
    {Admissible : ℕ -> Type*}
    {matchProb : ∀ C : ℕ, Admissible C -> ℝ -> ℝ}
    {totalSupply alpha : ℝ} (delta sigma : ℕ -> ℝ)
    (htotalSupply_lt_one : totalSupply < 1)
    (hdelta_nonneg : ∀ C, 0 ≤ delta C)
    (hsigma_nonneg : ∀ C, 0 ≤ sigma C)
    (hdelta_zero : Tendsto delta atTop (nhds 0))
    (hwindow : ∀ v : ℝ,
      ∀ᶠ C : ℕ in atTop, ∀ mu : Admissible C,
        theorem2TwoScaleRegularWindow totalSupply alpha (delta C)
          (theorem2_twoScaleEndpointError delta sigma C) (sigma C)
          (matchProb C mu v)) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v epsilon hepsilon_pos
  have hlower_tendsto := theorem2_twoScaleLowerError_tendsto_zero alpha
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hupper_tendsto := theorem2_twoScaleUpperError_tendsto_zero
    (totalSupply := totalSupply) (alpha := alpha) htotalSupply_lt_one
    hdelta_nonneg hsigma_nonneg hdelta_zero
  have hlower_small : ∀ᶠ C : ℕ in atTop,
      theorem2_twoScaleLowerError alpha (delta C)
        (theorem2_twoScaleEndpointError delta sigma C) (sigma C) < epsilon :=
    hlower_tendsto (isOpen_Iio.mem_nhds hepsilon_pos)
  have hupper_small : ∀ᶠ C : ℕ in atTop,
      theorem2_twoScaleUpperError totalSupply alpha (delta C)
        (theorem2_twoScaleEndpointError delta sigma C) (sigma C) < epsilon :=
    hupper_tendsto (isOpen_Iio.mem_nhds hepsilon_pos)
  filter_upwards [hwindow v, hlower_small, hupper_small] with C hC hlower hupper mu
  rcases hC mu with ⟨hlower_bound, hupper_bound⟩
  rw [abs_lt]
  constructor <;> linarith

end

end PG24NoisyMatchingMarkets
