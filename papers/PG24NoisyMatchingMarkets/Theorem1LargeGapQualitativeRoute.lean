import PG24NoisyMatchingMarkets.Theorem1LargeGapCaseAnalytic
import PG24NoisyMatchingMarkets.Theorem1LargeGapQualitative
import Mathlib.Tactic

/-!
# PG24 Theorem 1 Case 2 qualitative route

The large-gap branch has a polynomial low-side maximum estimate and a
qualitative high-side endpoint.  Combining them yields the qualitative
low-value integral conclusion that the paper's main theorem requires.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
For any actual cutoff sequence in the derived large-gap branch, upper-block
affordance over the low-value region tends to zero.  The high-side term is
qualitative: no single-draw moment or polynomial high-side rate is assumed.
-/
theorem theorem1_largeGap_upper_low_integral_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    {maxVariance : ℕ → ℝ} {beta gamma vS totalSupply : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
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
    Tendsto (fun C : ℕ =>
      ∫ value : ℝ,
        (Set.Iic vS).indicator
          (fun value => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (theorem1CutoffAtOrAboveBlock
              (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
              (theorem3RankedCutoffNat C (cutoff C)
                (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
            value (cutoff C)) value
        ∂valueLaw) atTop (nhds 0) := by
  rcases theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA_nonneg, hrate⟩
  let threshold : ℕ → ℝ := fun C =>
    theorem3RankedCutoffNat C (cutoff C)
      (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
      Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)
  let fullP : ℕ → ℝ → ℝ := fun C value =>
    cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)
  let q : ℕ → ℝ := fun C => fullP C (threshold C)
  have hq_tendsto : Tendsto q atTop (nhds 1) := by
    simpa [q, fullP, threshold] using
      (theorem1_ranked_largeGap_full_affordance_tendsto_one
        noiseLaw hbeta hgamma hvariance hlarge_gap)
  have hhigh_error_nonneg : ∀ C : ℕ, 0 ≤ 1 - q C := by
    intro C
    have hq_le_one : q C ≤ 1 := by
      dsimp [q, fullP]
      exact cutoffAffordanceProbability_le_one
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (threshold C) (cutoff C)
    linarith
  have hhigh_error_le_half : ∀ᶠ C : ℕ in atTop, 1 - q C ≤ 1 / 2 := by
    filter_upwards [hq_tendsto (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with C hqC
    change (1 / 2 : ℝ) < q C at hqC
    linarith
  have hfull_affordance : ∀ C : ℕ, ∀ value ∈ Set.Ioi (threshold C),
      1 - (1 - q C) ≤ fullP C value := by
    intro C value hvalue
    have hmono := cutoffAffordanceProbability_mono_value
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (active := Finset.univ) (cutoff := cutoff C)
      (v := threshold C) (w := value)
      (show threshold C ≤ value from le_of_lt hvalue)
    have hrewrite : 1 - (1 - q C) = q C := by ring
    rw [hrewrite]
    simpa [q, fullP] using hmono
  have hlow_error_nonneg : ∀ C : ℕ,
      0 ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := by
    intro C
    exact mul_nonneg hA_nonneg (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hintegral_bound : ∀ᶠ C : ℕ in atTop,
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
          2 * totalSupply * (1 - q C) := by
    filter_upwards [hrate, hhigh_error_le_half] with C hrateC hhalfC
    exact theorem1_iid_atOrAbove_low_integral_le_of_fullMax_low_and_full_high
      noiseLaw valueLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
      (hlow_error_nonneg C) (hhigh_error_nonneg C) hhalfC hrateC
      (hfull_affordance C) (hfull_capacity C) htail_normalization
  have hlow_zero : Tendsto
      (fun C : ℕ => A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
      atTop (nhds 0) := by
    have hpow : Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop (theorem1TailK_pos hbeta.1 hgamma)).comp
          tendsto_natCast_atTop_atTop)
    simpa using hpow.const_mul A
  have hhigh_zero : Tendsto (fun C : ℕ => 1 - q C) atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
        hq_tendsto)
  have htail_zero : Tendsto
      (fun C : ℕ => 2 * totalSupply * (1 - q C)) atTop (nhds 0) := by
    simpa [mul_assoc] using hhigh_zero.const_mul (2 * totalSupply)
  have hupper_zero : Tendsto
      (fun C : ℕ =>
        A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) +
          2 * totalSupply * (1 - q C)) atTop (nhds 0) :=
    by simpa using hlow_zero.add htail_zero
  have hintegral_nonneg : ∀ C : ℕ,
      0 ≤ ∫ value : ℝ,
        (Set.Iic vS).indicator
          (fun value => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (theorem1CutoffAtOrAboveBlock
              (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
              (theorem3RankedCutoffNat C (cutoff C)
                (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
            value (cutoff C)) value
        ∂valueLaw := by
    intro C
    apply integral_nonneg
    intro value
    by_cases hvalue : value ∈ Set.Iic vS
    · rw [Set.indicator_of_mem hvalue]
      exact cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (theorem1CutoffAtOrAboveBlock
          (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
          (theorem3RankedCutoffNat C (cutoff C)
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
        value (cutoff C)
    · simp [Set.indicator_of_notMem hvalue]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero (Filter.Eventually.of_forall hintegral_nonneg) hintegral_bound

end

end PG24NoisyMatchingMarkets
