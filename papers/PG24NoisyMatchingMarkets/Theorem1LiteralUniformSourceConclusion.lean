import PG24NoisyMatchingMarkets.Theorem1LargeGapConditional
import PG24NoisyMatchingMarkets.Theorem1LiteralAttenuationConclusion
import PG24NoisyMatchingMarkets.Theorem1LiteralDenseSourceRoute
import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedDichotomy
import Mathlib.Tactic

/-!
# PG24 Theorem 1 uniform literal source conclusion

This module keeps the quantifier order of the paper's attenuation theorem.
Every eventually-small estimate is proved simultaneously for every admissible
literal basic-model instance at a fixed market size.  It does not select a
sequence of stable matchings and does not use a diagonal argument.
-/

open Filter Topology MeasureTheory Asymptotics
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w

/-- The finite ranked dense-window / large-gap alternative is uniform over
all literal selected cutoffs at a fixed market size. -/
theorem theorem1_literal_uniform_denseWindow_or_large_gap_eventually
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {totalSupply alpha beta gamma : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
      (∃ start : ℕ,
        start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
            theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
              theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ∧
          theorem1TailDenseRankWindow
            (theorem3RankedCutoffNat C (inst C a).selectedCutoffVector) start
            (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
            (theorem1DenseDeviationRadius C beta gamma)) ∨
        theorem3RankedCutoffNat C (inst C a).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) : ℝ) *
            theorem1DenseDeviationRadius C beta gamma <
          theorem3RankedCutoffNat C (inst C a).selectedCutoffVector
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) := by
  filter_upwards [eventually_gt_atTop 0,
    theorem1DenseWindowCount_eventually_le_earlyPrefixRank hbeta hgamma]
      with C hC_pos hfit a
  exact theorem3_ranked_denseWindow_or_rounded_large_gap
    (inst C a).selectedCutoffVector hC_pos hfit

/-- The dense branch is uniform over the admissible literal selected cutoffs.
All asymptotic envelopes depend only on the fixed source parameters. -/
theorem theorem1_literal_uniform_dense_branch_eventually_small_of_holder
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta vS totalSupply : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    ∃ holderConstant gamma : ℝ,
      0 < gamma ∧
      0 ≤ holderConstant ∧
      (∀ (x delta : ℝ), 0 < delta →
        eta.real (Set.Ioo x (x + delta)) ≤
          holderConstant * Real.rpow delta gamma) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C, ∀ start : ℕ,
          start + theorem3DenseWindowCount C
              (theorem1TailPhi2 beta gamma) ≤
            theorem3DenseGapBlockCount C
                (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
              theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) →
          theorem1TailDenseRankWindow
              (theorem3RankedCutoffNat C (inst C a).selectedCutoffVector) start
              (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
              (theorem1DenseDeviationRadius C beta gamma) →
          eventMass
            ((inst C a).studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
              (inst C a).value outcome.1 ∈ Set.Iic vS ∧
                chosenInActive
                  ((inst C a).literal.demand.demandAt
                    (inst C a).literal.selectedCutoff)
                  (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon := by
  rcases hregular with ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder⟩
  refine ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder, ?_⟩
  have hcapacity_zero : Tendsto
      (fun C : ℕ => alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpower : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpower.const_mul alpha
  have hgroup_zero := theorem1_dense_group_error_envelope_tendsto_zero_of_beta
    noiseLaw hbeta hgamma hvariance
  have hholder_zero := theorem1_dense_holder_envelope_tendsto_zero
    (holderConstant := holderConstant) hbeta.1 hgamma
  have herror_zero := theorem1_dense_group_deviation_tendsto_zero_of_beta
    noiseLaw hbeta hgamma hvariance
  have hhigh_zero : Tendsto (fun C : ℕ =>
      2 * totalSupply *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)) atTop (nhds 0) := by
    simpa using herror_zero.const_mul (2 * totalSupply)
  let denseBound : ℕ → ℝ := fun C =>
    alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) +
      holderConstant * Real.rpow
        (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
      2 * totalSupply *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma)
  have hdenseBound_zero : Tendsto denseBound atTop (nhds 0) := by
    simpa [denseBound] using
      ((hcapacity_zero.add hgroup_zero).add hholder_zero).add hhigh_zero
  intro epsilon hepsilon
  have hdenseBound_small : ∀ᶠ C : ℕ in atTop, denseBound C < epsilon := by
    simpa using hdenseBound_zero (Iio_mem_nhds hepsilon)
  have hradius_le_half : ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤ 1 / 2 := by
    have hstrict : ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) < 1 / 2 := by
      simpa using herror_zero
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hstrict] with C hC
    linarith
  filter_upwards [eventually_ge_atTop 1, hdenseBound_small, hradius_le_half]
      with C hC_one hbound_small hradius a start hstart_window hdense
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  let upper : Finset (Fin (C + 1)) := theorem1CutoffAtOrAboveBlock
    Finset.univ (inst C a).selectedCutoffVector
    (theorem3RankedCutoffNat C (inst C a).selectedCutoffVector start)
  have hcount : (theorem1IntegerGroupCount upper
      (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) ≤
      3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma) :=
    theorem1_dense_group_count_le_three_rpow_of_one_le
      hbeta.1 hgamma hC_one upper
  have herror_nonneg : 0 ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin
          (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
        (theorem1DenseGroupCenter noiseLaw C beta gamma)
        (theorem1DenseDeviationRadius C beta gamma) :=
    theorem1_iid_topOrderDeviationProbability_nonneg
      (m := theorem1DenseGroupIndex C beta gamma + 1) noiseLaw _ _
  have hgroup_le :
      (theorem1IntegerGroupCount upper
        (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) ≤
      (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
        AppliedModelingLib.Matching.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
          (theorem1DenseGroupCenter noiseLaw C beta gamma)
          (theorem1DenseDeviationRadius C beta gamma) :=
    mul_le_mul_of_nonneg_right hcount herror_nonneg
  have hstatic := theorem1_literal_selected_dense_low_matched_mass_le_of_ranked_window
    noiseLaw eta (inst C a) hbeta.1 hgamma halpha_nonneg hholder hC_pos start
    hstart_window hdense hradius htail_normalization
  calc
    eventMass
        ((inst C a).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
          (inst C a).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C a).literal.demand.demandAt
                (inst C a).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        (theorem1IntegerGroupCount upper
          (theorem1DenseGroupIndex C beta gamma + 1) : ℝ) *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) +
        holderConstant * Real.rpow
          (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
        2 * totalSupply *
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin
              (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
            (theorem1DenseGroupCenter noiseLaw C beta gamma)
            (theorem1DenseDeviationRadius C beta gamma) := by
      simpa [upper] using hstatic
    _ ≤ denseBound C := by
      change _ ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          (3 * Real.rpow (C : ℝ) (1 - theorem1TailPhi2 beta gamma)) *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma) +
          holderConstant * Real.rpow
            (5 * theorem1DenseDeviationRadius C beta gamma) gamma +
          2 * totalSupply *
            AppliedModelingLib.Matching.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem1DenseGroupIndex C beta gamma + 1) => noiseLaw))
              (theorem1DenseGroupCenter noiseLaw C beta gamma)
              (theorem1DenseDeviationRadius C beta gamma)
      exact add_le_add_left
        (add_le_add_left (add_le_add_right hgroup_le _) _) _
    _ < epsilon := hbound_small

/-- The Case 2 upper-block integral estimate, with the instance quantifier
inside the eventual bound. -/
theorem theorem1_largeGap_upper_low_integral_uniform_eventually_small_conditional_of_beta
    {Admissible : ℕ → Type w}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {maxVariance : ℕ → ℝ} {beta gamma vS totalSupply : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (hfull_capacity : ∀ C : ℕ, ∀ a : Admissible C,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C a) ∂valueLaw) =
        totalSupply)
    (htail_normalization : valueLaw.real (Set.Ioi vS) = totalSupply) :
    ∀ epsilon : ℝ, 0 < epsilon →
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
    rw [← htail_normalization]
    exact measureReal_nonneg
  have htwo_totalSupply_nonneg : 0 ≤ 2 * totalSupply := by
    nlinarith
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
        mul_le_mul_of_nonneg_left hhighError_le_fraction htwo_totalSupply_nonneg
      _ ≤ epsilon / 2 := hfraction_budget
  have hlow_rate_small : ∀ᶠ C : ℕ in atTop,
      A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) < epsilon / 2 :=
    hlow_rate_zero (isOpen_Iio.mem_nhds (show (0 : ℝ) < epsilon / 2 by
      positivity))
  have hfull_endpoint :=
    theorem1_ranked_largeGap_full_affordance_eventually_conditional
      noiseLaw hbeta hgamma hvariance hhighError_pos
  filter_upwards [hrate, hlow_rate_small, hfull_endpoint]
      with C hrate_C hlow_C hendpoint_C a hlarge_gap
  have hfull_affordance : ∀ value ∈ Set.Ioi
      (theorem3RankedCutoffNat C (cutoff C a)
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
        Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)),
      1 - highError ≤ cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value (cutoff C a) := by
    intro value hvalue
    exact le_trans
      (le_of_lt (hendpoint_C (cutoff C a) hlarge_gap))
      (cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (show _ ≤ value from le_of_lt hvalue))
  have hintegral_bound :=
    theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
      noiseLaw valueLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C a)
      (mul_nonneg hA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _))
      (le_of_lt hhighError_pos) hhighError_le_half hrate_C hfull_affordance
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
      ∂valueLaw) ≤
        A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          2 * totalSupply * highError := hintegral_bound
    _ < epsilon := by linarith

/-- In the literal model, the uniform Case 2 bound applies to every selected
stable cutoff at once. -/
theorem theorem1_literal_uniform_largeGap_low_matched_mass_eventually_small_conditional
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta gamma vS totalSupply : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        theorem3RankedCutoffNat C (inst C a).selectedCutoffVector 0 +
            (theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma)
              (theorem1TailPhi3 beta gamma) : ℝ) *
              Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
          theorem3RankedCutoffNat C (inst C a).selectedCutoffVector
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) →
        eventMass
          ((inst C a).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
            (inst C a).value outcome.1 ∈ Set.Iic vS ∧
              chosenInActive
                ((inst C a).literal.demand.demandAt
                  (inst C a).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon := by
  have hfull_capacity : ∀ C : ℕ, ∀ a : Admissible C,
      (∫ value : ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C a).selectedCutoffVector ∂eta) = totalSupply := by
    intro C a
    exact (inst C a).theorem1_selected_full_affordance_integral_eq_totalSupply
  have hupper_small :=
    theorem1_largeGap_upper_low_integral_uniform_eventually_small_conditional_of_beta
      (Admissible := Admissible) noiseLaw eta hbeta hgamma hvariance
      (fun C a => (inst C a).selectedCutoffVector) hfull_capacity
      htail_normalization
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
  have hcomponents : ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
      eventMass
        ((inst C a).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
          (inst C a).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C a).literal.demand.demandAt
                (inst C a).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
        alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          ∫ value : ℝ,
            (Set.Iic vS).indicator
              (fun value => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (theorem1CutoffAtOrAboveBlock
                  (Finset.univ : Finset (Fin (C + 1)))
                  (inst C a).selectedCutoffVector
                  (theorem3RankedCutoffNat C (inst C a).selectedCutoffVector
                    (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
                value (inst C a).selectedCutoffVector) value
            ∂eta := by
    filter_upwards [eventually_gt_atTop 0] with C hC_pos a
    exact (inst C a).theorem1_selected_low_matched_mass_le_rankPrefix_components
      hbeta.1 hgamma hC_pos halpha_nonneg measurableSet_Iic
  intro epsilon hepsilon
  have hcapacity_small : ∀ᶠ C : ℕ in atTop,
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) < epsilon / 2 :=
    hcapacity_zero (isOpen_Iio.mem_nhds (show (0 : ℝ) < epsilon / 2 by
      positivity))
  have hupper_half := hupper_small (epsilon / 2) (by positivity)
  filter_upwards [hcomponents, hcapacity_small, hupper_half]
      with C hcomponents_C hcapacity_C hupper_C a hlarge_gap
  calc
    eventMass
        ((inst C a).studentLaw.prod
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
        (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
          (inst C a).value outcome.1 ∈ Set.Iic vS ∧
            chosenInActive
              ((inst C a).literal.demand.demandAt
                (inst C a).literal.selectedCutoff)
              (Finset.univ : Finset (Fin (C + 1))) outcome) ≤
      alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
        ∫ value : ℝ,
          (Set.Iic vS).indicator
            (fun value => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem1CutoffAtOrAboveBlock
                (Finset.univ : Finset (Fin (C + 1)))
                (inst C a).selectedCutoffVector
                (theorem3RankedCutoffNat C (inst C a).selectedCutoffVector
                  (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
              value (inst C a).selectedCutoffVector) value
          ∂eta := hcomponents_C a
    _ < epsilon := by linarith [hcapacity_C, hupper_C a hlarge_gap]

/-- The literal repaired lower-tail matched mass is uniformly small over all
admissible selected stable instances. -/
theorem theorem1_literal_uniform_low_matched_mass_eventually_small_of_beta_holder
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        eventMass
          ((inst C a).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
            (inst C a).value outcome.1 ∈ Set.Iic vS ∧
              chosenInActive
                ((inst C a).literal.demand.demandAt
                  (inst C a).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon := by
  rcases theorem1_literal_uniform_dense_branch_eventually_small_of_holder
      (Admissible := Admissible) noiseLaw eta inst hbeta hvariance
      halpha_nonneg hregular htail_normalization with
    ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder, hdense⟩
  have hgeometry := theorem1_literal_uniform_denseWindow_or_large_gap_eventually
    (Admissible := Admissible) noiseLaw eta inst hbeta.1 hgamma
  have hlarge :=
    theorem1_literal_uniform_largeGap_low_matched_mass_eventually_small_conditional
      (Admissible := Admissible) noiseLaw eta inst hbeta hgamma hvariance
      halpha_nonneg htail_normalization
  intro epsilon hepsilon
  filter_upwards [hdense epsilon hepsilon, hlarge epsilon hepsilon, hgeometry]
      with C hdense_C hlarge_C hgeometry_C a
  rcases hgeometry_C a with hdense_case | hlarge_case
  · rcases hdense_case with ⟨start, hstart, hwindow⟩
    exact hdense_C a start hstart hwindow
  · exact hlarge_C a hlarge_case

/-- Direct uniform literal source conclusion for PG24 Theorem 1.  The
eventual cutoff is shared by all admissible literal instances at each market
size; no selected sequence is used. -/
theorem theorem1_literal_uniform_selected_attenuation_source_clauses_of_beta_holder
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    (∀ value epsilon : ℝ, value < vS → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C a).selectedCutoffVector < epsilon) ∧
    (∀ value epsilon : ℝ, vS < value → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        1 - epsilon < cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C a).selectedCutoffVector) := by
  have hlowMatched :=
    theorem1_literal_uniform_low_matched_mass_eventually_small_of_beta_holder
      (Admissible := Admissible) noiseLaw eta inst hbeta hvariance
      halpha_nonneg hregular htail_normalization
  constructor
  · intro value epsilon hvalue hepsilon
    have hinterval : 0 < eta.real (Set.Ioo value vS) :=
      theorem1_low_interval_mass_pos_of_connected_support eta hconnected hregular
        htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue
    have hmass_small := hlowMatched
      (epsilon * eta.real (Set.Ioo value vS)) (mul_pos hepsilon hinterval)
    filter_upwards [hmass_small] with C hmass_C a
    letI : IsProbabilityMeasure (inst C a).studentLaw :=
      (inst C a).studentLaw_isProbability
    have hmatched_eq_integral :
        eventMass
            ((inst C a).studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
              (inst C a).value outcome.1 ∈ Set.Iic vS ∧
                chosenInActive
                  ((inst C a).literal.demand.demandAt
                    (inst C a).literal.selectedCutoff)
                  (Finset.univ : Finset (Fin (C + 1))) outcome) =
          ∫ w : ℝ,
            (Set.Iic vS).indicator
              (fun w => cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) w
                (inst C a).selectedCutoffVector) w
            ∂eta := by
      exact theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
        (inst C a).studentLaw (inst C a).value (inst C a).value_measurable eta
        (inst C a).value_marginal noiseLaw (inst C a).selectedCutoffVector
        ((inst C a).literal.demand.demandAt (inst C a).literal.selectedCutoff)
        (inst C a).selected_demand_none_iff_no_crossed
        (inst C a).selected_demand_feasible measurableSet_Iic
    have hinterval_bound :=
      theorem1_low_affordance_interval_mass_mul_le_low_integral
        eta noiseLaw (inst C a).selectedCutoffVector hvalue
    have hintegral_small :
        (∫ w : ℝ,
          (Set.Iic vS).indicator
            (fun w => cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) w
              (inst C a).selectedCutoffVector) w
          ∂eta) < epsilon * eta.real (Set.Ioo value vS) := by
      rw [← hmatched_eq_integral]
      exact hmass_C a
    have hproduct : eta.real (Set.Ioo value vS) *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C a).selectedCutoffVector <
        eta.real (Set.Ioo value vS) * epsilon := by
      calc
        eta.real (Set.Ioo value vS) *
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) value
              (inst C a).selectedCutoffVector ≤
            ∫ w : ℝ,
              (Set.Iic vS).indicator
                (fun w => cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) w
                  (inst C a).selectedCutoffVector) w
              ∂eta := hinterval_bound
        _ < epsilon * eta.real (Set.Ioo value vS) := hintegral_small
        _ = eta.real (Set.Ioo value vS) * epsilon := by ring
    exact lt_of_mul_lt_mul_left hproduct hinterval.le
  · intro value epsilon hvalue hepsilon
    have hinterval : 0 < eta.real (Set.Ioo vS value) :=
      theorem1_high_interval_mass_pos_of_connected_support eta hconnected hregular
        htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue
    have hmass_small := hlowMatched
      (epsilon * eta.real (Set.Ioo vS value)) (mul_pos hepsilon hinterval)
    filter_upwards [hmass_small] with C hmass_C a
    letI : IsProbabilityMeasure (inst C a).studentLaw :=
      (inst C a).studentLaw_isProbability
    have hmatched_eq_unmatched :=
      (inst C a).theorem1_selected_low_matched_mass_eq_high_unmatched_mass
        vS htail_normalization
    have hunmatched_eq_integral :
        eventMass
            ((inst C a).studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
              (inst C a).value outcome.1 ∈ Set.Ioi vS ∧
                ¬ chosenInActive
                  ((inst C a).literal.demand.demandAt
                    (inst C a).literal.selectedCutoff)
                  (Finset.univ : Finset (Fin (C + 1))) outcome) =
          ∫ w : ℝ,
            (Set.Ioi vS).indicator
              (fun w => 1 - cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) w
                (inst C a).selectedCutoffVector) w
            ∂eta := by
      exact theorem1_source_model_value_restricted_unmatched_mass_eq_integral_affordance_complement
        (inst C a).studentLaw (inst C a).value (inst C a).value_measurable eta
        (inst C a).value_marginal
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (inst C a).selectedCutoffVector
        ((inst C a).literal.demand.demandAt (inst C a).literal.selectedCutoff)
        (inst C a).theorem1_selected_chosenInAll_iff_affordance measurableSet_Ioi
    have hinterval_bound :=
      theorem1_high_unaffordance_interval_mass_mul_le_high_integral
        eta noiseLaw (inst C a).selectedCutoffVector hvalue
    have hintegral_small :
        (∫ w : ℝ,
          (Set.Ioi vS).indicator
            (fun w => 1 - cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) w
              (inst C a).selectedCutoffVector) w
          ∂eta) < epsilon * eta.real (Set.Ioo vS value) := by
      rw [← hunmatched_eq_integral, ← hmatched_eq_unmatched]
      exact hmass_C a
    have hproduct : eta.real (Set.Ioo vS value) *
        (1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          (inst C a).selectedCutoffVector) <
        eta.real (Set.Ioo vS value) * epsilon := by
      calc
        eta.real (Set.Ioo vS value) *
            (1 - cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) value
              (inst C a).selectedCutoffVector) ≤
            ∫ w : ℝ,
              (Set.Ioi vS).indicator
                (fun w => 1 - cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) w
                  (inst C a).selectedCutoffVector) w
              ∂eta := hinterval_bound
        _ < epsilon * eta.real (Set.Ioo vS value) := hintegral_small
        _ = eta.real (Set.Ioo vS value) * epsilon := by ring
    have hfailure_lt : 1 - cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        (inst C a).selectedCutoffVector < epsilon :=
      lt_of_mul_lt_mul_left hproduct hinterval.le
    linarith

end

end PG24NoisyMatchingMarkets
