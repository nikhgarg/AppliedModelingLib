import PG24NoisyMatchingMarkets.Theorem1LargeGapConditional
import PG24NoisyMatchingMarkets.Theorem1LiteralAttenuationConclusion
import PG24NoisyMatchingMarkets.Theorem1LiteralDenseSourceRoute
import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedDichotomy
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal source conclusion

The finite ranked-cutoff dichotomy is joined with its two literal source-model
branches.  Both branches prove the same low matched-mass conclusion, so the
pointwise source theorem follows without a preselected branch or a hidden
ordering of college names.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
The repaired literal basic-model version of PG24 Theorem 1.  It uses the
source beta-max condition, the stated Holder/connected-support value law,
literal iid sampling, literal demand and clearing, and the strict
upper-tail supply normalization.  The large-gap branch supplies qualitative
convergence; this theorem does not claim the source's unsupported common
polynomial rate for that branch.
-/
theorem theorem1_literal_selected_attenuationConclusion_of_beta_holder
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    theorem1_attenuationConclusion
      (fun C : ℕ => fun value : ℝ => cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        (inst C).selectedCutoffVector)
      vS := by
  rcases theorem1_literal_selected_dense_branch_eventually_small_of_holder
      noiseLaw eta inst hbeta hvariance halpha_nonneg hregular
      htail_normalization with
    ⟨holderConstant, gamma, hgamma, hholder_nonneg, hholder, hdense⟩
  let lowMatched : ℕ → ℝ := fun C =>
    eventMass
      ((inst C).studentLaw.prod
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
      (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
        (inst C).value outcome.1 ∈ Set.Iic vS ∧
          chosenInActive
            ((inst C).literal.demand.demandAt
              (inst C).literal.selectedCutoff)
            (Finset.univ : Finset (Fin (C + 1))) outcome)
  let denseCase : ℕ → Prop := fun C =>
    ∃ start : ℕ,
      start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
          theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
            theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ∧
        theorem1TailDenseRankWindow
          (theorem3RankedCutoffNat C (inst C).selectedCutoffVector) start
          (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
          (theorem1DenseDeviationRadius C beta gamma)
  let largeGapCase : ℕ → Prop := fun C =>
    theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
        (theorem3DenseGapBlockCount C
          (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) : ℝ) *
          Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
      theorem3RankedCutoffNat C (inst C).selectedCutoffVector
        (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))
  have hgeometry : ∀ᶠ C : ℕ in atTop,
      denseCase C ∨ largeGapCase C := by
    filter_upwards [theorem1_literal_selected_denseWindow_or_large_gap_eventually
      noiseLaw eta inst hbeta.1 hgamma] with C hC
    simpa [denseCase, largeGapCase, theorem1DenseDeviationRadius] using hC
  have hdense_small : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, denseCase C → lowMatched C < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hdense epsilon hepsilon] with C hC hdense_C
    rcases hdense_C with ⟨start, hstart, hwindow⟩
    simpa [lowMatched] using hC start hstart hwindow
  have hlargeGap_small : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, largeGapCase C → lowMatched C < epsilon := by
    intro epsilon hepsilon
    filter_upwards [theorem1_literal_selected_largeGap_low_matched_mass_eventually_small_conditional
      noiseLaw eta inst hbeta hgamma hvariance halpha_nonneg
      htail_normalization epsilon hepsilon] with C hC hlargeGap_C
    simpa [lowMatched, largeGapCase] using hC hlargeGap_C
  have hnonneg : ∀ C : ℕ, 0 ≤ lowMatched C := by
    intro C
    exact measureReal_nonneg
  have hlowMatched : Tendsto lowMatched atTop (nhds 0) :=
    theorem1_tendsto_zero_of_eventually_branch_epsilon
      lowMatched denseCase largeGapCase hnonneg hdense_small hlargeGap_small
      hgeometry
  simpa [lowMatched] using
    (theorem1_literal_selected_attenuationConclusion_of_low_matched_mass_tendsto_zero
      noiseLaw eta inst htail_normalization hconnected hregular
      htotalSupply_pos htotalSupply_lt_one hlowMatched)

end

end PG24NoisyMatchingMarkets
