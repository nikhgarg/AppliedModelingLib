import PG24NoisyMatchingMarkets.Theorem1LargeGapQualitative
import PG24NoisyMatchingMarkets.Theorem1LargeGapCaseAnalytic
import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedCutoffBridge
import Mathlib.Tactic

/-!
# PG24 Theorem 1 conditional Case 2 route

The ranked dense-window / large-gap split is made independently at each
market size.  This module records the Case 2 estimates in the corresponding
eventual conditional form, so they can be combined with the dense branch
without assuming that one branch holds eventually on its own.
-/

open Filter Topology MeasureTheory Asymptotics
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
At all sufficiently large market sizes, every cutoff vector satisfying the
literal ranked large-gap alternative has near-certain full-market affordance
at the Case 2 threshold.
-/
theorem theorem1_ranked_largeGap_full_affordance_eventually_conditional
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ -> ℝ} {beta gamma epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop, ∀ cutoff : Fin (C + 1) -> ℝ,
      theorem3RankedCutoffNat C cutoff 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) ->
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedCutoffNat C cutoff
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
            Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma))
          cutoff := by
  let rank : ℕ -> ℕ := fun C =>
    theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)
  let gapLower : ℕ -> ℝ := fun C =>
    (theorem3DenseGapBlockCount C
      (theorem1TailPhi2 beta gamma)
      (theorem1TailPhi3 beta gamma) : ℝ) *
      Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)
  let mean : ℕ -> ℝ :=
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
  let slack : ℕ -> ℝ := fun C => mean C +
    Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)
  let value : ∀ C : ℕ, (Fin (C + 1) -> ℝ) -> ℝ := fun C cutoff =>
    theorem3RankedCutoffNat C cutoff (rank C) - slack C
  have hmean_log : Tendsto
      (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0) := by
    dsimp [mean]
    exact theorem3_iidExpectedMaximum_div_log_tendsto_zero_of_beta
      noiseLaw hbeta hvariance
  have hslack_little : slack =o[atTop] gapLower := by
    simpa [slack, mean, gapLower] using
      (theorem1Tail_mean_add_phi4_isLittleO_roundedLargeGapScale
        hbeta.1 hgamma hmean_log)
  have hgap_toTop : Tendsto gapLower atTop atTop := by
    simpa [gapLower, theorem1TailLargeGapExponent] using
      (theorem3DenseGapBlockCount_mul_rpow_tendsto_atTop
        (denseExponent := theorem1TailPhi2 beta gamma)
        (prefixExponent := theorem1TailPhi3 beta gamma)
        (width := theorem1TailPhi1 beta gamma)
        (gapExponent := theorem1TailLargeGapExponent beta gamma)
        (theorem1TailPhi2_pos hbeta.1 hgamma).le
        (theorem1TailPhi1_neg hbeta.1 hgamma)
        (theorem1TailLargeGapExponent_pos hbeta.1 hgamma)
        (by rfl))
  have hslack_sub_gap :
      Tendsto (fun C : ℕ => slack C - gapLower C) atTop atBot :=
    theorem3_slack_sub_gap_tendsto_atBot_of_isLittleO hgap_toTop hslack_little
  rcases Filter.eventually_atBot.1
      (AppliedModelingLib.Probability.eventually_one_sub_lt_upperTailMass_atBot
        noiseLaw hepsilon) with ⟨bound, htail_bound⟩
  have hscalar : ∀ᶠ C : ℕ in atTop, slack C - gapLower C ≤ bound :=
    tendsto_atBot.mp hslack_sub_gap bound
  filter_upwards [hscalar] with C hscalar_C cutoff hlarge_gap
  let lowCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let highCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hsemantic_gap :
      gapLower C < cutoff highCollege - cutoff lowCollege := by
    dsimp [highCollege, lowCollege]
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff (rank C),
      ← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff 0]
    have hgap' : theorem3RankedCutoffNat C cutoff 0 + gapLower C <
        theorem3RankedCutoffNat C cutoff (rank C) := by
      simpa [rank, gapLower] using hlarge_gap
    linarith
  have hvalue_below_high_rank :
      cutoff highCollege - value C cutoff ≤ slack C := by
    dsimp [highCollege]
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff (rank C)]
    dsimp [value]
    linarith
  have hlow_cutoff_sub_value :
      cutoff lowCollege - value C cutoff ≤ bound := by
    calc
      cutoff lowCollege - value C cutoff ≤ slack C - gapLower C := by
        linarith
      _ ≤ bound := hscalar_C
  have hsingle_high :
      1 - epsilon <
        singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C cutoff) cutoff lowCollege := by
    rw [singleCollegeAffordanceProbability,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_eq_upperTailMass]
    exact htail_bound _ hlow_cutoff_sub_value
  have hsingle_le :
      singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C cutoff) cutoff lowCollege ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1)))
          (value C cutoff) cutoff := by
    simpa only [singleCollegeAffordanceProbability,
      cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (by simp)
        (value C cutoff) cutoff)
  have hthreshold :
      theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C +
            Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)) =
        theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
          Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma) := by
    ring
  have hresult := lt_of_lt_of_le hsingle_high hsingle_le
  dsimp [value, rank, mean, slack] at hresult
  simp only [← Real.rpow_eq_pow] at hresult
  rw [hthreshold] at hresult
  exact hresult

/--
The Case 2 upper-cutoff-block low-value integral is eventually small whenever
the literal ranked large-gap alternative holds at that market size.
-/
theorem theorem1_largeGap_upper_low_integral_eventually_small_conditional_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {maxVariance : ℕ -> ℝ} {beta gamma vS totalSupply : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    {cutoff : ∀ C : ℕ, Fin (C + 1) -> ℝ}
    (hfull_capacity : ∀ C : ℕ,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C) ∂valueLaw) =
        totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply) :
    ∀ epsilon : ℝ, 0 < epsilon ->
      ∀ᶠ C : ℕ in atTop,
        theorem3RankedCutoffNat C (cutoff C) 0 +
            (theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma)
              (theorem1TailPhi3 beta gamma) : ℝ) *
              Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
          theorem3RankedCutoffNat C (cutoff C)
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) ->
        (∫ value : ℝ,
          (Set.Iic vS).indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
                (theorem3RankedCutoffNat C (cutoff C)
                  (theorem3EarlyPrefixRank C
                    (theorem1TailPhi3 beta gamma))))
              value (cutoff C)) value
          ∂valueLaw) < epsilon := by
  rcases theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hrate⟩
  have hlow_rate_zero : Tendsto
      (fun C : ℕ => A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpow.const_mul A
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rw [← hfull_capacity 0]
    exact integral_nonneg (fun value =>
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (0 + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (0 + 1))) value (cutoff 0))
  intro epsilon hepsilon
  let highError : ℝ := min (1 / 4) (epsilon / (4 * (totalSupply + 1)))
  have hdenom_pos : 0 < 4 * (totalSupply + 1) := by
    nlinarith
  have hquotient_pos : 0 < epsilon / (4 * (totalSupply + 1)) :=
    div_pos hepsilon hdenom_pos
  have hhighError_pos : 0 < highError := by
    dsimp [highError]
    exact lt_min (by norm_num) hquotient_pos
  have hhighError_le_half : highError ≤ 1 / 2 := by
    dsimp [highError]
    exact le_trans (min_le_left _ _) (by norm_num)
  have hhighError_le_fraction :
      highError ≤ epsilon / (4 * (totalSupply + 1)) := by
    dsimp [highError]
    exact min_le_right _ _
  have hfraction_budget :
      2 * totalSupply * (epsilon / (4 * (totalSupply + 1))) ≤ epsilon / 2 := by
    have hdenom_ne : 4 * (totalSupply + 1) ≠ 0 := ne_of_gt hdenom_pos
    calc
      2 * totalSupply * (epsilon / (4 * (totalSupply + 1))) =
          (2 * totalSupply * epsilon) / (4 * (totalSupply + 1)) := by
        field_simp [hdenom_ne]
      _ ≤ epsilon / 2 := by
        apply (div_le_iff₀ hdenom_pos).mpr
        nlinarith
  have hhigh_budget : 2 * totalSupply * highError ≤ epsilon / 2 := by
    calc
      2 * totalSupply * highError ≤
          2 * totalSupply * (epsilon / (4 * (totalSupply + 1))) :=
        mul_le_mul_of_nonneg_left hhighError_le_fraction (by nlinarith)
      _ ≤ epsilon / 2 := hfraction_budget
  have hlow_rate_small : ∀ᶠ C : ℕ in atTop,
      A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) < epsilon / 2 :=
    hlow_rate_zero (isOpen_Iio.mem_nhds (show (0 : ℝ) < epsilon / 2 by
      positivity))
  have hfull_endpoint :=
    theorem1_ranked_largeGap_full_affordance_eventually_conditional
      noiseLaw hbeta hgamma hvariance hhighError_pos
  filter_upwards [hrate, hlow_rate_small, hfull_endpoint]
      with C hrate_C hlow_C hendpoint_C hlarge_gap
  have hfull_affordance : ∀ value ∈ Set.Ioi
      (theorem3RankedCutoffNat C (cutoff C)
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
        Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)),
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value (cutoff C) := by
    intro value hvalue
    exact le_trans
      (le_of_lt (hendpoint_C (cutoff C) hlarge_gap))
      (cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (show _ ≤ value from le_of_lt hvalue))
  have hintegral_bound :=
    theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
      noiseLaw valueLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
      (mul_nonneg hA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (le_of_lt hhighError_pos) hhighError_le_half hrate_C hfull_affordance
      (hfull_capacity C) htail_normalization
  calc
    (∫ value : ℝ,
      (Set.Iic vS).indicator
        (fun value => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem1CutoffAtOrAboveBlock
            (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
            (theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
          value (cutoff C)) value
      ∂valueLaw) ≤
        A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          2 * totalSupply * highError := hintegral_bound
    _ < epsilon := by linarith

/--
For the literal selected source model, the Case 2 alternative implies an
eventually small low-value matched mass at that same market size.
-/
theorem theorem1_literal_selected_largeGap_low_matched_mass_eventually_small_conditional
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ -> ℝ} {alpha beta gamma vS totalSupply : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    ∀ epsilon : ℝ, 0 < epsilon ->
      ∀ᶠ C : ℕ in atTop,
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
            (theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma)
              (theorem1TailPhi3 beta gamma) : ℝ) *
              Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
          theorem3RankedCutoffNat C (inst C).selectedCutoffVector
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) ->
        eventMass
          ((inst C).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
            (inst C).value outcome.1 ∈ Set.Iic vS ∧
              chosenInActive
                ((inst C).literal.demand.demandAt
                  (inst C).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon := by
  letI : IsProbabilityMeasure (inst 0).studentLaw :=
    (inst 0).studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← (inst 0).value_marginal]
    exact Measure.isProbabilityMeasure_map
      (inst 0).value_measurable.aemeasurable
  have hfull_capacity : ∀ C : ℕ,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C).selectedCutoffVector ∂eta) = totalSupply := by
    intro C
    exact (inst C).theorem1_selected_full_affordance_integral_eq_totalSupply
  have hupper_small :=
    theorem1_largeGap_upper_low_integral_eventually_small_conditional_of_beta
      noiseLaw eta hbeta hgamma hvariance hfull_capacity htail_normalization
  have hcapacity_zero : Tendsto
      (fun C : ℕ => alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpow.const_mul alpha
  have hcomponents : ∀ᶠ C : ℕ in atTop,
      eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  (inst C).selectedCutoffVector
                  (theorem3RankedCutoffNat C (inst C).selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value (inst C).selectedCutoffVector) value
            ∂eta := by
    filter_upwards [eventually_gt_atTop 0] with C hC_pos
    exact (inst C).theorem1_selected_low_matched_mass_le_rankPrefix_components
      hbeta.1 hgamma hC_pos halpha_nonneg measurableSet_Iic
  intro epsilon hepsilon
  have hcapacity_small : ∀ᶠ C : ℕ in atTop,
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) < epsilon / 2 :=
    hcapacity_zero (isOpen_Iio.mem_nhds (show (0 : ℝ) < epsilon / 2 by
      positivity))
  have hupper_half := hupper_small (epsilon / 2) (by positivity)
  filter_upwards [hcomponents, hcapacity_small, hupper_half]
      with C hcomponents_C hcapacity_C hupper_C hlarge_gap
  calc
    eventMass
        ((inst C).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
          (inst C).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C).literal.demand.demandAt
                (inst C).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  (inst C).selectedCutoffVector
                  (theorem3RankedCutoffNat C (inst C).selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value (inst C).selectedCutoffVector) value
            ∂eta := hcomponents_C
    _ < epsilon := by
      linarith [hcapacity_C, hupper_C hlarge_gap]

end

end PG24NoisyMatchingMarkets
