import PG24NoisyMatchingMarkets.Theorem2TwoScaleFailureRatioBridge

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

theorem theorem2_selectedStable_large_cutoff_atTop_of_boundary
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type v}
    (selected : ∀ C : ℕ, Admissible C →
      { mu : (Mseq C).Matching // (Mseq C).Stable mu })
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (boundaryCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (hboundary_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, B ≤ boundaryCutoff C a)
    (hboundary_le_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          boundaryCutoff C a ≤ cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c) :
    ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ c ∈ large C a,
        B ≤ cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) c := by
  intro B
  filter_upwards [hboundary_atTop B, hboundary_le_large] with
    C hboundaryC hlargeC a c hc
  exact le_trans (hboundaryC a) (hlargeC a c hc)

theorem theorem2_selectedStable_large_highTailRate_of_boundary
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type v}
    (selected : ∀ C : ℕ, Admissible C →
      { mu : (Mseq C).Matching // (Mseq C).Stable mu })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (boundaryCutoff : ∀ C : ℕ, Admissible C → ℝ)
    {vHigh sigma : ℝ}
    (hboundary_le_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          boundaryCutoff C a ≤ cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c)
    (hboundary_highTail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (boundaryCutoff C a - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ c ∈ large C a,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ) := by
  filter_upwards [hboundary_le_large, hboundary_highTail] with
    C hlargeC htailC a c hc
  exact
    le_trans
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right (hlargeC a c hc) vHigh))
      (htailC a)

theorem theorem2_selectedStable_eventually_largeFailureRatio_of_source_boundary_geometry
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type v}
    (selected : ∀ C : ℕ, Admissible C →
      { mu : (Mseq C).Matching // (Mseq C).Stable mu })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (boundaryCutoff : ∀ C : ℕ, Admissible C → ℝ)
    {vLow vHigh r sigma : ℝ}
    (hv : vLow < vHigh) (hr_pos : 0 < r) (hr_le_one : r ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (hboundary_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, B ≤ boundaryCutoff C a)
    (hboundary_le_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          boundaryCutoff C a ≤ cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c)
    (hboundary_highTail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (boundaryCutoff C a - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ c ∈ large C a,
        Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c - vHigh)) /
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c - vLow)) ∧
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c - vLow) ∧
          1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c - vLow) ≤ 1 := by
  let selectedCutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a => cutoffOut C
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
  have hcutoff_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a, B ≤ selectedCutoff C a c := by
    simpa [selectedCutoff] using
      (theorem2_selectedStable_large_cutoff_atTop_of_boundary
        Mseq Iseq selected cutoffOut boundaryCutoff hboundary_atTop
        hboundary_le_large)
  have hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (selectedCutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    simpa [selectedCutoff] using
      (theorem2_selectedStable_large_highTailRate_of_boundary
        Mseq Iseq selected noiseLaw cutoffOut boundaryCutoff hboundary_le_large
        hboundary_highTail)
  simpa [selectedCutoff] using
    (theorem2_eventually_largeFailureRatio_of_longTailed_unboundedCutoffGeometry
      noiseLaw hlong hv hr_pos hr_le_one hsigma_nonneg hcutoff_atTop
      hhigh_le_sigma_div)

theorem theorem2_selectedStable_exists_endpoint_with_eventual_largeFailureRatio_of_source_boundary_geometry_after_scale
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type v}
    (selected : ∀ C : ℕ, Admissible C →
      { mu : (Mseq C).Matching // (Mseq C).Stable mu })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (boundaryCutoff : ∀ C : ℕ, Admissible C → ℝ)
    {tol sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma)
    (hv : vLow < vHigh)
    (hboundary_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, B ≤ boundaryCutoff C a)
    (hboundary_le_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          boundaryCutoff C a ≤ cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c)
    (hboundary_highTail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (boundaryCutoff C a - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      1 - Real.exp (-(2 * r * sigma)) < tol ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c - vHigh)) /
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2) c - vLow)) ∧
            0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c - vLow) ∧
            1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c - vLow) ≤ 1 := by
  rcases theorem2_exists_endpoint_error_after_scale htol_pos hsigma_pos with
    ⟨r, hr_pos, hr_le_one, hgap⟩
  refine ⟨r, hr_pos, hr_le_one, hgap, ?_⟩
  exact
    theorem2_selectedStable_eventually_largeFailureRatio_of_source_boundary_geometry
      Mseq Iseq selected noiseLaw hlong cutoffOut boundaryCutoff hv hr_pos
      hr_le_one hsigma_pos.le hboundary_atTop hboundary_le_large
      hboundary_highTail

end

end PG24NoisyMatchingMarkets
