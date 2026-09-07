import PG24NoisyMatchingMarkets.Theorem2TwoScaleLargeBlockBridge

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

theorem theorem2_eventually_largeFailureRatio_of_longTailed_unboundedCutoffGeometry
    {Admissible : ℕ → Type u}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {vLow vHigh r sigma : ℝ}
    (hv : vLow < vHigh) (hr_pos : 0 < r) (hr_le_one : r ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (hcutoff_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a, B ≤ cutoff C a c)
    (hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ c ∈ large C a,
        Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh)) /
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C a c - vLow)) ∧
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) ∧
          1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) ≤ 1 := by
  have htail_pos_atTop :
      ∀ᶠ x : ℝ in atTop,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw x :=
    hlong.eventually_pos
      (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x)
  rcases Filter.eventually_atTop.1 htail_pos_atTop with
    ⟨posFloor, hposFloor⟩
  have htail_lt_one_atTop :
      ∀ᶠ x : ℝ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw x < 1 :=
    AppliedModelingLib.Probability.eventually_upperTailMass_lt_one_atTop noiseLaw
  rcases Filter.eventually_atTop.1 htail_lt_one_atTop with
    ⟨oneFloor, honeFloor⟩
  have hhigh_pos :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vHigh) := by
    filter_upwards [hcutoff_atTop (posFloor + vHigh)] with C hcutoffC a c hc
    exact hposFloor (cutoff C a c - vHigh) (by
      linarith [hcutoffC a c hc])
  have hlow_failure_pos :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) := by
    filter_upwards [hcutoff_atTop (oneFloor + vHigh)] with C hcutoffC a c hc
    have htail_lt_one :
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) < 1 :=
      honeFloor (cutoff C a c - vLow) (by
        have hle_high : oneFloor ≤ cutoff C a c - vHigh := by
          linarith [hcutoffC a c hc]
        linarith)
    linarith
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Filter.eventually_atTop.1
      (LongTailedSurvival.eventually_ratio_gt hlong hd hr_pos) with
    ⟨x0, hx0⟩
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        sigma / ((C + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
    AppliedModelingLib.Math.eventually_const_div_nat_succ_le_half sigma
  filter_upwards
    [hhigh_pos, hlow_failure_pos, hcutoff_atTop (x0 + vHigh),
      hhigh_le_sigma_div, hsmall] with
    C hhigh_posC hlow_failure_posC hcutoffC hhigh_bound hsmallC a c hc
  have hC_pos : 0 < ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos C
  have hq_nonneg :
      0 ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoff C a c - vHigh) :=
    AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
  have hq_half :
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoff C a c - vHigh) ≤ 1 / 2 :=
    le_trans (hhigh_bound a c hc) hsmallC
  have hq_le_one :
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoff C a c - vHigh) ≤ 1 := by
    linarith
  have htail :
      1 - r <
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C a c - vLow) /
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vHigh) := by
    have hx_ge : x0 ≤ cutoff C a c - vHigh := by
      linarith [hcutoffC a c hc]
    have hratio := hx0 (cutoff C a c - vHigh) hx_ge
    simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hratio
  have hscalar_floor :
      Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
        (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C a c - vHigh)) /
          (1 - (1 - r) * AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vHigh)) :=
    AppliedModelingLib.Math.exp_neg_two_mul_mul_div_le_one_sub_div_one_sub_one_sub_mul
      (epsilon := r) (sigma := sigma) (C := ((C + 1 : ℕ) : ℝ))
      (q := AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoff C a c - vHigh))
      hr_pos.le hr_le_one hsigma_nonneg hC_pos hq_nonneg hq_half
      (hhigh_bound a c hc)
  refine ⟨?_, hlow_failure_posC a c hc, ?_⟩
  · exact
      failureRatio_floor_of_tailRatio_div_floor
        (hqHigh_pos := hhigh_posC a c hc)
        (hqHigh_le_one := hq_le_one)
        (hfloor := hscalar_floor)
        (htail_ratio := le_of_lt htail)
        (hlow_failure_pos := hlow_failure_posC a c hc)
  · have hlow_nonneg :
        0 ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C a c - vLow) :=
      AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
    linarith

theorem theorem2_eventually_largeFailureRatio_of_longTailed_endpointGeometry
    {Admissible : ℕ → Type u}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh r sigma : ℝ}
    (hv : vLow < vHigh) (hr_pos : 0 < r) (hr_le_one : r ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (hlower_atTop :
      Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          lowerCutoff C ≤ cutoff C a c)
    (hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ c ∈ large C a,
        Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh)) /
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C a c - vLow)) ∧
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) ∧
          1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C a c - vLow) ≤ 1 := by
  have hcutoff_atTop :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a, B ≤ cutoff C a c := by
    intro B
    have hlower :
        ∀ᶠ C : ℕ in atTop, B - vHigh ≤ lowerCutoff C - vHigh :=
      hlower_atTop (Filter.eventually_atTop.2 ⟨B - vHigh, fun x hx => hx⟩)
    filter_upwards [hlower, hcutoff_lower] with C hlowerC hcutoffC a c hc
    linarith [hlowerC, hcutoffC a c hc]
  exact
    theorem2_eventually_largeFailureRatio_of_longTailed_unboundedCutoffGeometry
      noiseLaw hlong hv hr_pos hr_le_one hsigma_nonneg hcutoff_atTop
      hhigh_le_sigma_div

theorem theorem2_exists_endpoint_with_eventual_largeFailureRatio_after_scale
    {Admissible : ℕ → Type u}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {large : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {tol sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma)
    (hv : vLow < vHigh)
    (hlower_atTop :
      Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          lowerCutoff C ≤ cutoff C a c)
    (hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      1 - Real.exp (-(2 * r * sigma)) < tol ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          Real.exp (-(2 * r * sigma / ((C + 1 : ℕ) : ℝ))) ≤
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C a c - vHigh)) /
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C a c - vLow)) ∧
            0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vLow) ∧
            1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C a c - vLow) ≤ 1 := by
  rcases theorem2_exists_endpoint_error_after_scale htol_pos hsigma_pos with
    ⟨r, hr_pos, hr_le_one, hproduct_gap⟩
  refine ⟨r, hr_pos, hr_le_one, hproduct_gap, ?_⟩
  exact theorem2_eventually_largeFailureRatio_of_longTailed_endpointGeometry
    noiseLaw hlong hv hr_pos hr_le_one hsigma_pos.le hlower_atTop
    hcutoff_lower hhigh_le_sigma_div

theorem theorem2_selectedStable_eventually_largeFailureRatio_of_longTailed_endpointGeometry
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
    {lowerCutoff : ℕ → ℝ} {vLow vHigh r sigma : ℝ}
    (hv : vLow < vHigh) (hr_pos : 0 < r) (hr_le_one : r ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (hlower_atTop :
      Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          lowerCutoff C ≤ cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c)
    (hhigh_le_sigma_div :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c - vHigh) ≤
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
  have hcutoff_lower' :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          lowerCutoff C ≤ selectedCutoff C a c := by
    simpa [selectedCutoff] using hcutoff_lower
  have hhigh_le_sigma_div' :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ large C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (selectedCutoff C a c - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ) := by
    simpa [selectedCutoff] using hhigh_le_sigma_div
  simpa [selectedCutoff] using
    (theorem2_eventually_largeFailureRatio_of_longTailed_endpointGeometry
      noiseLaw hlong hv hr_pos hr_le_one hsigma_nonneg hlower_atTop
      hcutoff_lower' hhigh_le_sigma_div')

end

end PG24NoisyMatchingMarkets
