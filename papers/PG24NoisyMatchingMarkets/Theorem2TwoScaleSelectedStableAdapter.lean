import PG24NoisyMatchingMarkets.Theorem2TwoScaleAmplificationClosure

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

theorem theorem2_twoScaleRegularWindow_of_selectedStable_sourceModel
    {StudentTypeSeq : ℕ → Type u}
    [∀ C, MeasurableSpace (StudentTypeSeq C)]
    (Mseq : ∀ C : ℕ,
      CutoffMarket
        (StudentTypeSeq C × (Fin (C + 1) → ℝ))
        (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type v}
    (selected : ∀ C : ℕ, Admissible C →
      { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (C : ℕ) (a : Admissible C)
    (studentLaw : Measure (StudentTypeSeq C)) [IsProbabilityMeasure studentLaw]
    (value : StudentTypeSeq C → ℝ) (hvalue : Measurable value)
    (valueLaw : Measure ℝ) [IsProbabilityMeasure valueLaw]
    (hvalue_marginal : Measure.map value studentLaw = valueLaw)
    (small large : Finset (Fin (C + 1)))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin (C + 1))) )
    {largeRegion smallRegion : Set ℝ}
    {totalSupply alpha delta endpoint sigma vLow vHigh vStar v : ℝ}
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
    (hv_low : vLow ≤ v) (hv_high : v ≤ vHigh) (hv_star : v ≤ vStar)
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c - vLow) ≤ 1)
    (hdemand_none_iff_no_crossed :
      ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
        ∀ outcome : StudentTypeSeq C × (Fin (C + 1) → ℝ),
          (Mseq C).demandAt P outcome = none ↔
            ¬ cutoffCrossedOn (Finset.univ : Finset (Fin (C + 1)))
              (noisyScore (value outcome.1) outcome.2) (cutoffOut C P))
    (hchosen_feasible :
      ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
        ∀ (outcome : StudentTypeSeq C × (Fin (C + 1) → ℝ))
          (college : Fin (C + 1)),
          (Mseq C).demandAt P outcome = some college ->
            cutoffOut C P college < value outcome.1 + outcome.2 college)
    (hchoice_mass :
      ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
        ∀ active : Finset (Fin (C + 1)),
          choiceMass
            (studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            ((Mseq C).demandAt P) active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (htotal_capacity :
      (∑ c : Fin (C + 1), (Mseq C).capacity c) = totalSupply)
    (hsmall_card : (small.card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_regular : capacityRegular (Mseq C).capacity alpha (C + 1))
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) v
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)) ) := by
  let P : (Mseq C).Cutoff :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  have hP : (Mseq C).MarketClearing P := by
    simpa [P] using
      ((Iseq C).marketClearingCutoffOfStable_marketClearing (selected C a).2)
  have hn_pos : 0 < ((C + 1 : ℕ) : ℝ) := by
    positivity
  have hclearing : ∀ c : Fin (C + 1),
      (Mseq C).aggregateDemand P c = (Mseq C).capacity c := by
    intro c
    exact (Kseq C).aggregateDemand_eq_capacity hP c
  have hdemand_none :
      ∀ outcome : StudentTypeSeq C × (Fin (C + 1) → ℝ),
        (Mseq C).demandAt P outcome = none ↔
          ¬ cutoffCrossedOn (Finset.univ : Finset (Fin (C + 1)))
            (noisyScore (value outcome.1) outcome.2) (cutoffOut C P) :=
    hdemand_none_iff_no_crossed P hP
  have hchosen :
      ∀ (outcome : StudentTypeSeq C × (Fin (C + 1) → ℝ))
        (college : Fin (C + 1)),
        (Mseq C).demandAt P outcome = some college ->
          cutoffOut C P college < value outcome.1 + outcome.2 college :=
    hchosen_feasible P hP
  have hglobal_choice_mass :
      choiceMass
          (studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          ((Mseq C).demandAt P) (Finset.univ : Finset (Fin (C + 1))) =
        ∑ c ∈ (Finset.univ : Finset (Fin (C + 1))),
          (Mseq C).aggregateDemand P c :=
    hchoice_mass P hP (Finset.univ : Finset (Fin (C + 1)))
  have hsmall_choice_mass :
      choiceMass
          (studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          ((Mseq C).demandAt P) small =
        ∑ c ∈ small, (Mseq C).aggregateDemand P c :=
    hchoice_mass P hP small
  have hlarge_choice_mass :
      choiceMass
          (studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          ((Mseq C).demandAt P) large =
        ∑ c ∈ large, (Mseq C).aggregateDemand P c :=
    hchoice_mass P hP large
  have hfailure_ratio' :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C P c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C P c - vLow)) := by
    simpa [P] using hfailure_ratio
  have hlow_failure_pos' :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoffOut C P c - vLow) := by
    simpa [P] using hlow_failure_pos
  have hlow_failure_le_one' :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoffOut C P c - vLow) ≤ 1 := by
    simpa [P] using hlow_failure_le_one
  simpa [P] using
    (theorem2_twoScaleCutoffRegularWindow_of_sourceModel_checked_bounds
      studentLaw value hvalue valueLaw hvalue_marginal noiseLaw small large
      hdisjoint hcover (cutoffOut C P) hlargeRegion_meas hlargeRegion_mass
      hlargeRegion_ge hlargeRegion_le_high hsmallRegion_meas hsmallRegion_mass
      hsmallRegion_ge hsmallRegion_le_high hdelta_pos htotalSupply_nonneg
      htotalSupply_delta_lt_one hdenom_nonneg hendpoint_nonneg hsigma_nonneg
      hn_pos hv_low hv_high hv_star hfailure_ratio' hlow_failure_pos'
      hlow_failure_le_one' ((Mseq C).demandAt P) hdemand_none hchosen
      ((Mseq C).aggregateDemand P) (Mseq C).capacity hglobal_choice_mass
      hsmall_choice_mass hlarge_choice_mass hclearing htotal_capacity hsmall_card
      halpha_nonneg hcapacity_regular hden_pos)

end

end PG24NoisyMatchingMarkets
