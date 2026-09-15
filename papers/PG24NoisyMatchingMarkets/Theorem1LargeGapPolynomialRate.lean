import PG24NoisyMatchingMarkets.Theorem1LargeGapQualitative
import PG24NoisyMatchingMarkets.Theorem1LargeGapCaseAnalytic
import PG24NoisyMatchingMarkets.Theorem1SourceProofHelpers
import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Tactic

/-!
# PG24 large-gap polynomial rate

The printed Case-2 high-side rate uses a one-draw Chebyshev step.  The source
beta-max premise controls only maxima, so this module makes the additional
source-used finite second-moment condition for one noise draw explicit.  The
result combines that condition with the exact rounded large-gap scale; it does
not replace the qualitative theorem available under beta-max concentration
alone.
-/

open Filter Topology MeasureTheory Asymptotics
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
Under the one-draw finite-second-moment clarification, the large-gap branch
has the polynomial full-affordance rate printed in Proposition 7(ii).

The constant is explicit up to the one-draw variance.  The source's beta-max
condition remains responsible for controlling the expected maximum in the
moving threshold; it is not used as a surrogate one-draw moment condition.
-/
theorem theorem1_ranked_largeGap_full_affordance_eventually_le_source_rate_conditional_of_one_draw_second_moment
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hone_draw : MemLp (fun x : ℝ => x) 2 noiseLaw) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ cutoff : Fin (C + 1) → ℝ,
        theorem3RankedCutoffNat C cutoff 0 +
            (theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma)
              (theorem1TailPhi3 beta gamma) : ℝ) *
              Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
          theorem3RankedCutoffNat C cutoff
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) →
        1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1)))
            (theorem3RankedCutoffNat C cutoff
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
              Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma))
            cutoff ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  let rank : ℕ → ℕ := fun C =>
    theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)
  let gapLower : ℕ → ℝ := fun C =>
    (theorem3DenseGapBlockCount C
      (theorem1TailPhi2 beta gamma)
      (theorem1TailPhi3 beta gamma) : ℝ) *
      Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma)
  let mean : ℕ → ℝ :=
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
  let slack : ℕ → ℝ := fun C => mean C +
    Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)
  let gapExponent : ℝ := theorem1TailLargeGapExponent beta gamma
  let oneDrawMean : ℝ := ∫ x : ℝ, x ∂noiseLaw
  let oneDrawVariance : ℝ := ProbabilityTheory.variance (fun x : ℝ => x) noiseLaw
  let rateConstant : ℝ := 1024 * oneDrawVariance
  refine ⟨rateConstant, mul_nonneg (by norm_num)
    (ProbabilityTheory.variance_nonneg (fun x : ℝ => x) noiseLaw), ?_⟩
  have hmean_log : Tendsto
      (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0) := by
    dsimp [mean]
    exact theorem3_iidExpectedMaximum_div_log_tendsto_zero_of_beta
      noiseLaw hbeta hvariance
  have hslack_little : slack =o[atTop] gapLower := by
    simpa [slack, mean, gapLower] using
      (theorem1Tail_mean_add_phi4_isLittleO_roundedLargeGapScale
        hbeta.1 hgamma hmean_log)
  have hgapExponent_pos : 0 < gapExponent := by
    simpa [gapExponent] using theorem1TailLargeGapExponent_pos hbeta.1 hgamma
  have hscale_lower : ∀ᶠ C : ℕ in atTop,
      (1 / 8 : ℝ) * Real.rpow (C : ℝ) gapExponent ≤ gapLower C := by
    simpa [gapLower, gapExponent] using
      (theorem3DenseGapBlockCount_mul_rpow_eventually_ge_eighth_rpow
        (denseExponent := theorem1TailPhi2 beta gamma)
        (prefixExponent := theorem1TailPhi3 beta gamma)
        (width := theorem1TailPhi1 beta gamma)
        (gapExponent := theorem1TailLargeGapExponent beta gamma)
        (theorem1TailPhi2_pos hbeta.1 hgamma).le
        (theorem1TailPhi1_neg hbeta.1 hgamma)
        (theorem1TailLargeGapExponent_pos hbeta.1 hgamma) rfl)
  have hpower_toTop : Tendsto (fun C : ℕ => Real.rpow (C : ℝ) gapExponent)
      atTop atTop :=
    (tendsto_rpow_atTop hgapExponent_pos).comp tendsto_natCast_atTop_atTop
  have hslack_bound := hslack_little.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hpower_large : ∀ᶠ C : ℕ in atTop,
      max 1 (-32 * oneDrawMean) ≤ Real.rpow (C : ℝ) gapExponent :=
    hpower_toTop.eventually_ge_atTop _
  filter_upwards [hscale_lower, hslack_bound, hpower_large] with
      C hscale_C hslack_C hpower_C cutoff hlarge_gap_C
  have hC_one : 1 ≤ C := by
    by_contra hnot
    have hC_zero : C = 0 := by omega
    subst C
    have hcontradiction : (1 : ℝ) ≤ (0 : ℝ) := by
      calc
        (1 : ℝ) ≤ max 1 (-32 * oneDrawMean) := le_max_left _ _
        _ ≤ Real.rpow (0 : ℝ) gapExponent := by simpa using hpower_C
        _ = 0 := Real.zero_rpow (ne_of_gt hgapExponent_pos)
    norm_num [Real.zero_rpow (ne_of_gt hgapExponent_pos)] at hcontradiction
  have hC_pos : 0 < (C : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC_one)
  have hpower_pos : 0 < Real.rpow (C : ℝ) gapExponent :=
    Real.rpow_pos_of_pos hC_pos _
  have hgap_nonneg : 0 ≤ gapLower C := by
    exact le_trans (mul_nonneg (by norm_num) (le_of_lt hpower_pos)) hscale_C
  have hslack_le_half_gap : slack C ≤ gapLower C / 2 := by
    calc
      slack C ≤ |slack C| := le_abs_self _
      _ = ‖slack C‖ := by simp only [Real.norm_eq_abs]
      _ ≤ (1 / 2 : ℝ) * ‖gapLower C‖ := hslack_C
      _ = gapLower C / 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgap_nonneg]
        ring
  have hmean_lower : -(1 / 32 : ℝ) * Real.rpow (C : ℝ) gapExponent ≤
      oneDrawMean := by
    have hraw : -32 * oneDrawMean ≤ Real.rpow (C : ℝ) gapExponent :=
      le_trans (le_max_right _ _) hpower_C
    nlinarith
  let lowCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let highCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let value : ℝ := theorem3RankedCutoffNat C cutoff (rank C) - slack C
  let radius : ℝ := (1 / 32 : ℝ) * Real.rpow (C : ℝ) gapExponent
  have hradius_pos : 0 < radius := by
    dsimp [radius]
    positivity
  have hthreshold_le : cutoff lowCollege - value ≤ oneDrawMean - radius := by
    dsimp [lowCollege, highCollege, value, radius]
    have hlarge_gap' : theorem3RankedCutoffNat C cutoff 0 + gapLower C <
        theorem3RankedCutoffNat C cutoff (rank C) := by
      simpa [rank, gapLower] using hlarge_gap_C
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff 0]
    have hbelow_gap :
        theorem3RankedCutoffNat C cutoff 0 -
            (theorem3RankedCutoffNat C cutoff (rank C) - slack C) ≤
          -gapLower C + slack C := by
      linarith
    have hscale_half : -gapLower C + slack C ≤
        -(1 / 16 : ℝ) * Real.rpow (C : ℝ) gapExponent := by
      linarith
    have hmean_shift : -(1 / 16 : ℝ) * Real.rpow (C : ℝ) gapExponent ≤
        oneDrawMean - (1 / 32 : ℝ) * Real.rpow (C : ℝ) gapExponent := by
      linarith
    exact hbelow_gap.trans (hscale_half.trans hmean_shift)
  have hchebyshev :
      1 - oneDrawVariance / radius ^ 2 ≤
        noiseLaw.real (Set.Ioi (oneDrawMean - radius)) := by
    simpa [oneDrawVariance, oneDrawMean] using
      (AppliedModelingLib.one_sub_le_measureReal_Ioi_integral_sub_of_variance
        noiseLaw hone_draw hradius_pos)
  have hsingle_lower :
      1 - oneDrawVariance / radius ^ 2 ≤
        singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) value cutoff
          lowCollege := by
    calc
      1 - oneDrawVariance / radius ^ 2 ≤
          noiseLaw.real (Set.Ioi (oneDrawMean - radius)) := hchebyshev
      _ ≤ noiseLaw.real (Set.Ioi (cutoff lowCollege - value)) :=
        measureReal_mono (μ := noiseLaw)
          (Set.Ioi_subset_Ioi hthreshold_le) (measure_ne_top noiseLaw _)
      _ = singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) value cutoff
          lowCollege := by
        rw [singleCollegeAffordanceProbability,
          AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_eq_upperTailMass]
        rfl
  have hsingle_le_full :
      singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) value cutoff
          lowCollege ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value cutoff := by
    simpa only [singleCollegeAffordanceProbability, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (by simp)
        value cutoff)
  have hfailure :
      1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value cutoff ≤
        oneDrawVariance / radius ^ 2 := by
    linarith
  have hradius_sq : radius ^ 2 =
      (1 / 1024 : ℝ) * (Real.rpow (C : ℝ) gapExponent) ^ 2 := by
    dsimp [radius]
    ring
  have hrate_raw : oneDrawVariance / radius ^ 2 ≤
      rateConstant * Real.rpow (C : ℝ) (-2 * gapExponent) := by
    rw [hradius_sq]
    have hpower_ne : Real.rpow (C : ℝ) gapExponent ≠ 0 := ne_of_gt hpower_pos
    calc
      oneDrawVariance /
          ((1 / 1024 : ℝ) * (Real.rpow (C : ℝ) gapExponent) ^ 2) =
          (1024 * oneDrawVariance) /
            (Real.rpow (C : ℝ) gapExponent) ^ 2 := by
        field_simp [hpower_ne]
      _ ≤ (1024 * oneDrawVariance) *
          Real.rpow (C : ℝ) (-0 - 2 * gapExponent) := by
        simpa using
          (theorem1Tail_variance_div_rpow_window_sq_le
            (C := (C : ℝ)) (beta := 0) (window := gapExponent)
            (variance := 1024 * oneDrawVariance)
            (A := 1024 * oneDrawVariance) hC_pos (by simp))
      _ = rateConstant * Real.rpow (C : ℝ) (-2 * gapExponent) := by
        have hzero : (-0 - 2 * gapExponent : ℝ) = -2 * gapExponent := by ring
        rw [hzero]
  have hsource_exponent : -2 * gapExponent = -theorem1TailK beta gamma := by
    simp only [gapExponent, theorem1TailLargeGapExponent]
    rw [← theorem1Tail_case2_gap_exp_eq_neg_K hbeta.1 hgamma]
    ring
  have hrate : oneDrawVariance / radius ^ 2 ≤
      rateConstant * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    simpa [hsource_exponent] using hrate_raw
  have hthreshold_eq : value =
      theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
        Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma) := by
    dsimp [value, rank, slack, mean]
    ring
  rw [← hthreshold_eq]
  exact hfailure.trans hrate

/-- The global large-gap form follows by applying the conditional rate to
the supplied sequence of cutoff vectors. -/
theorem theorem1_ranked_largeGap_full_affordance_eventually_le_source_rate_of_one_draw_second_moment
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta gamma : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hone_draw : MemLp (fun x : ℝ => x) 2 noiseLaw)
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (cutoff C)
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
        1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1)))
            (theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
              Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma))
            (cutoff C) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem1_ranked_largeGap_full_affordance_eventually_le_source_rate_conditional_of_one_draw_second_moment
      noiseLaw hbeta hgamma hvariance hone_draw with ⟨A, hA, hrate⟩
  refine ⟨A, hA, ?_⟩
  filter_upwards [hrate, hlarge_gap] with C hrate_C hlarge_gap_C
  exact hrate_C (cutoff C) hlarge_gap_C

/-- Uniform conditional rate form of Proposition 8.  The cutoff vector may
vary over an admissible family, while the eventual index and rate constant
remain common to that family. -/
theorem theorem1_largeGap_upper_low_integral_uniform_eventually_le_source_rate_conditional_of_one_draw_second_moment
    {Admissible : ℕ → Type w}
    (noiseLaw valueLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure valueLaw]
    {maxVariance : ℕ → ℝ} {beta gamma vS totalSupply : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hone_draw : MemLp (fun x : ℝ => x) 2 noiseLaw)
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (hfull_capacity : ∀ C : ℕ, ∀ a : Admissible C,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C a) ∂valueLaw) =
        totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        theorem3RankedCutoffNat C (cutoff C a) 0 +
            (theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma)
              (theorem1TailPhi3 beta gamma) : ℝ) *
              Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
          theorem3RankedCutoffNat C (cutoff C a)
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) →
        (∫ value : ℝ,
          (Set.Iic vS).indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1))) (cutoff C a)
                (theorem3RankedCutoffNat C (cutoff C a)
                  (theorem3EarlyPrefixRank C
                    (theorem1TailPhi3 beta gamma))))
              value (cutoff C a)) value
          ∂valueLaw) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
      noiseLaw hbeta hgamma hvariance with ⟨lowA, hlowA_nonneg, hlow_rate⟩
  rcases theorem1_ranked_largeGap_full_affordance_eventually_le_source_rate_conditional_of_one_draw_second_moment
      noiseLaw hbeta hgamma hvariance hone_draw with ⟨highA, hhighA_nonneg, hhigh_rate⟩
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rw [← htail_normalization]
    exact measureReal_nonneg
  have hpow_to_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
        tendsto_natCast_atTop_atTop)
  have hhigh_small : ∀ᶠ C : ℕ in atTop,
      highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) ≤ 1 / 2 := by
    have hlimit : Tendsto (fun C : ℕ =>
        highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds (highA * 0)) := hpow_to_zero.const_mul highA
    have hstrict : ∀ᶠ C : ℕ in atTop,
        highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) < 1 / 2 := by
      simpa using hlimit (Iio_mem_nhds (by norm_num : highA * 0 < (1 / 2 : ℝ)))
    filter_upwards [hstrict] with C hC
    exact le_of_lt hC
  refine ⟨lowA + 2 * totalSupply * highA,
    add_nonneg hlowA_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      htotalSupply_nonneg) hhighA_nonneg), ?_⟩
  filter_upwards [hlow_rate, hhigh_rate, hhigh_small] with
      C hlow_C hhigh_C hhigh_half a hlarge_gap
  let pivot : ℝ := theorem3RankedCutoffNat C (cutoff C a)
    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))
  let threshold : ℝ := pivot -
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
    Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)
  let lowError : ℝ := lowA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))
  let highError : ℝ := highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))
  have hfull_affordance : ∀ value ∈ Set.Ioi threshold,
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value (cutoff C a) := by
    intro value hvalue
    have hthreshold_rate_raw : 1 ≤ highError +
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) threshold (cutoff C a) := by
      dsimp [threshold, pivot, highError]
      simpa only [← Real.rpow_eq_pow] using
        (sub_le_iff_le_add.mp (hhigh_C (cutoff C a) hlarge_gap))
    have hthreshold_rate : 1 - highError ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) threshold (cutoff C a) := by
      exact sub_le_iff_le_add.mpr (by linarith [hthreshold_rate_raw])
    exact hthreshold_rate.trans
      (cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) (le_of_lt hvalue))
  have hintegral :=
    theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
      noiseLaw valueLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C a)
      (mul_nonneg hlowA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (mul_nonneg hhighA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (by simpa [highError] using hhigh_half)
      (by simpa [pivot, threshold] using hlow_C) hfull_affordance
      (hfull_capacity C a) htail_normalization
  calc
    (∫ value : ℝ,
      (Set.Iic vS).indicator
        (fun value => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem1CutoffAtOrAboveBlock
            (Finset.univ : Finset (Fin (C + 1))) (cutoff C a)
            (theorem3RankedCutoffNat C (cutoff C a)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
          value (cutoff C a)) value
      ∂valueLaw) ≤ lowError + 2 * totalSupply * highError := by
        simpa [pivot, lowError, highError] using hintegral
    _ = (lowA + 2 * totalSupply * highA) *
        Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
        dsimp [lowError, highError]
        ring

/--
The Proposition 8 low-value integral inherits the source `C^-K` rate once
both Case-2 endpoints use their actual probability mechanisms: the full iid
maximum on the low side and the one-draw lower-tail bound on the high side.
-/
theorem theorem1_largeGap_upper_low_integral_eventually_le_source_rate_of_one_draw_second_moment
    (noiseLaw valueLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure valueLaw]
    {maxVariance : ℕ → ℝ} {beta gamma vS totalSupply : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hone_draw : MemLp (fun x : ℝ => x) 2 noiseLaw)
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (hfull_capacity : ∀ C : ℕ,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C) ∂valueLaw) =
        totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply)
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (cutoff C)
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ C : ℕ in atTop,
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
          ∂valueLaw) ≤
          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
  rcases theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
      noiseLaw hbeta hgamma hvariance with ⟨lowA, hlowA_nonneg, hlow_rate⟩
  rcases theorem1_ranked_largeGap_full_affordance_eventually_le_source_rate_of_one_draw_second_moment
      noiseLaw hbeta hgamma hvariance hone_draw hlarge_gap with
      ⟨highA, hhighA_nonneg, hhigh_rate⟩
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rw [← hfull_capacity 0]
    exact integral_nonneg (fun value =>
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (0 + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (0 + 1))) value (cutoff 0))
  have hpow_to_zero : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
        tendsto_natCast_atTop_atTop)
  have hhigh_to_zero : Tendsto
      (fun C : ℕ => highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    simpa using hpow_to_zero.const_mul highA
  have hhigh_small : ∀ᶠ C : ℕ in atTop,
      highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) ≤ 1 / 2 := by
    filter_upwards [hhigh_to_zero
      (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with C hC
    exact le_of_lt hC
  refine ⟨lowA + 2 * totalSupply * highA,
    add_nonneg hlowA_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      htotalSupply_nonneg) hhighA_nonneg), ?_⟩
  filter_upwards [hlow_rate, hhigh_rate, hhigh_small] with
      C hlow_C hhigh_C hhigh_half
  let pivot : ℝ := theorem3RankedCutoffNat C (cutoff C)
    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))
  let threshold : ℝ := pivot -
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
    Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)
  let lowError : ℝ := lowA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))
  let highError : ℝ := highA * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))
  have hfull_affordance : ∀ value ∈ Set.Ioi threshold,
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value (cutoff C) := by
    intro value hvalue
    have hthreshold_rate_raw : 1 ≤ highError +
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) threshold (cutoff C) := by
      dsimp [threshold, pivot, highError]
      simpa only [← Real.rpow_eq_pow] using
        (sub_le_iff_le_add.mp hhigh_C)
    have hthreshold_rate : 1 - highError ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) threshold (cutoff C) := by
      exact sub_le_iff_le_add.mpr (by linarith [hthreshold_rate_raw])
    exact hthreshold_rate.trans
      (cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) (le_of_lt hvalue))
  have hintegral :=
    theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
      noiseLaw valueLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
      (mul_nonneg hlowA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (mul_nonneg hhighA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (by simpa [highError] using hhigh_half)
      (by simpa [pivot, threshold] using hlow_C) hfull_affordance
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
      ∂valueLaw) ≤ lowError + 2 * totalSupply * highError := by
        simpa [pivot, lowError, highError] using hintegral
    _ = (lowA + 2 * totalSupply * highA) *
        Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
        dsimp [lowError, highError]
        ring

end

end PG24NoisyMatchingMarkets
