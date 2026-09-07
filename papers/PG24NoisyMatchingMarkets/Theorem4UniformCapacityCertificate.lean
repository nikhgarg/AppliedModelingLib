import PG24NoisyMatchingMarkets.Theorem4IntegratedCapacity
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Uniform Capacity Certificate

The analytic low-cutoff crossing argument is independent of the surrounding
matching-market carrier.  This module states that fact directly over arbitrary
local cutoff vectors, so the eventual threshold is uniform across the
extended paper's varying broader economies.
-/

open Filter Topology
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The endpoint-preserving Theorem 4 capacity certificate, stated without a
fixed sequence of local markets.  Once the long-tailed analytic parameters
are selected, it applies to every local cutoff vector of the given size.
-/
theorem exists_theorem4_uniform_floor_pow_integral_capacity_certificate_at_vHigh_of_longTailed
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (eta : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure eta]
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ cutoff : Fin (C + 1) → ℝ,
            epsilonFloorSplitIndex (tol / 2) C <
                (lowCutoffIndexSet cutoff
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card →
              totalSupply <
                ∫ v : ℝ,
                  1 -
                    (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                      ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - v)) ^
                      (lowCutoffIndexSet cutoff
                        (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card
                  ∂eta := by
  let p : ℝ := (1 + max totalSupply 0) / 2
  have hmax_nonneg : 0 ≤ max totalSupply 0 := le_max_right _ _
  have hmax_lt_one : max totalSupply 0 < 1 :=
    max_lt htotalSupply_lt_one (by norm_num)
  have hp_pos : 0 < p := by
    dsimp [p]
    linarith
  have hp_lt_one : p < 1 := by
    dsimp [p]
    linarith
  have htotalSupply_lt_p : totalSupply < p := by
    have hle : totalSupply ≤ max totalSupply 0 := le_max_left _ _
    dsimp [p]
    linarith
  have hscaledSupply_lt_one : totalSupply / p < 1 :=
    (div_lt_one hp_pos).mpr htotalSupply_lt_p
  have hvalue_tail :
      ∀ᶠ valueFloor : ℝ in atBot,
        p < AppliedModelingLib.Probability.upperTailMass eta valueFloor :=
    (AppliedModelingLib.Probability.upperTailMass_tendsto_one_atBot eta)
      (isOpen_Ioi.mem_nhds hp_lt_one)
  have hvalue_choice :
      ∀ᶠ valueFloor : ℝ in atBot,
        valueFloor < vHigh ∧
          p < AppliedModelingLib.Probability.upperTailMass eta valueFloor := by
    filter_upwards [Filter.eventually_lt_atBot vHigh, hvalue_tail] with
      valueFloor hlt htail
    exact ⟨hlt, htail⟩
  rcases hvalue_choice.exists with
    ⟨valueFloor, hvalueFloor_lt, hvalue_tail_floor⟩
  have htail_le_valueMass :
      AppliedModelingLib.Probability.upperTailMass eta valueFloor ≤
        eta.real (Set.Ici valueFloor) := by
    simpa [AppliedModelingLib.Probability.upperTailMass] using
      (MeasureTheory.measureReal_mono (μ := eta) Set.Ioi_subset_Ici_self
        (MeasureTheory.measure_ne_top eta _))
  have hvalueMass : p ≤ eta.real (Set.Ici valueFloor) :=
    le_of_lt (lt_of_lt_of_le hvalue_tail_floor htail_le_valueMass)
  have hdelta_pos : 0 < tol / 2 := by
    linarith
  rcases exists_positive_tail_scale_of_totalSupply_lt_one
      (delta := tol / 2) (totalSupply := totalSupply / p)
      hdelta_pos hscaledSupply_lt_one with ⟨tau, htau_pos, hcapacity_gap⟩
  let sigma : ℝ := 4 * tau
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    positivity
  let quantile : ℕ → ℝ :=
    fun C => theorem4HighTailQuantile noiseLaw sigma C
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        (1 - (1 / 2 : ℝ)) * (sigma / (((C + 1 : ℕ) : ℝ))) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw (quantile C) := by
    simpa [quantile] using
      (theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_of_longTailed
        noiseLaw hlong hsigma_pos (by norm_num) (by norm_num))
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hbound_zero :
      Tendsto (fun C : ℕ => sigma / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto sigma
  have hquantile_upper :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw (quantile C) ≤
          sigma / (((C + 1 : ℕ) : ℝ)) := by
    simpa [quantile] using
      (theorem4HighTailQuantile_upperTailMass_le_eventually
        noiseLaw hsigma_pos)
  have hquantile_atTop : Tendsto quantile atTop atTop :=
    AppliedModelingLib.Probability.tendsto_atTop_of_upperTailMass_le_tendsto_zero
      noiseLaw
      (hlong.eventually_pos
        (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x))
      hbound_zero hquantile_upper
  have hfloor_atTop :
      Tendsto (fun C : ℕ => (vHigh + quantile C) - vHigh) atTop atTop := by
    have heq : (fun C : ℕ => (vHigh + quantile C) - vHigh) = quantile := by
      funext C
      ring
    rw [heq]
    exact hquantile_atTop
  have hratio :
      ∀ᶠ C : ℕ in atTop,
        1 - (1 / 2 : ℝ) <
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((vHigh + quantile C) - valueFloor) /
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((vHigh + quantile C) - vHigh) :=
    LongTailedSurvival.eventually_value_ratio_gt hlong hvalueFloor_lt
      (by norm_num) hfloor_atTop
  have htail :
      ∀ᶠ C : ℕ in atTop,
        tau / (((C + 1 : ℕ) : ℝ)) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            ((vHigh + quantile C) - valueFloor) := by
    filter_upwards [hquantile_tail, hratio] with C hquantile_tail_C hratio_C
    let denominator : ℝ := ((C + 1 : ℕ) : ℝ)
    let upperHigh : ℝ :=
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        ((vHigh + quantile C) - vHigh)
    let upperLow : ℝ :=
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        ((vHigh + quantile C) - valueFloor)
    have hdenominator_pos : 0 < denominator := by
      dsimp [denominator]
      exact_mod_cast Nat.succ_pos C
    have hquantile_scaled : 2 * (tau / denominator) ≤ upperHigh := by
      calc
        2 * (tau / denominator) =
            (1 - (1 / 2 : ℝ)) * (sigma / denominator) := by
          dsimp [sigma]
          ring
        _ ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw (quantile C) := by
          simpa [denominator] using hquantile_tail_C
        _ = upperHigh := by
          dsimp [upperHigh]
          congr 1
          ring
    have htwice_tail_pos : 0 < 2 * (tau / denominator) := by
      positivity
    have hupperHigh_pos : 0 < upperHigh :=
      lt_of_lt_of_le htwice_tail_pos hquantile_scaled
    have hratio' : (1 / 2 : ℝ) < upperLow / upperHigh := by
      dsimp [upperLow, upperHigh]
      norm_num at hratio_C ⊢
      exact hratio_C
    have hhalf_upperHigh_lt : (1 / 2 : ℝ) * upperHigh < upperLow :=
      (lt_div_iff₀ hupperHigh_pos).mp hratio'
    have htail_scaled : tau / denominator ≤ (1 / 2 : ℝ) * upperHigh := by
      nlinarith [hquantile_scaled]
    exact le_trans htail_scaled hhalf_upperHigh_lt.le
  have hcross :=
    pg24_eventually_upperTail_split_crossing_of_scalar_lower_static_gap
      (Admissible := fun _ : ℕ => Unit) noiseLaw
      (delta := tol / 2) (tau := tau)
      (totalSupply := totalSupply / p)
      (lowerCutoff := fun C (_ : Unit) => vHigh + quantile C)
      (eventValue := fun _C (_ : Unit) => valueFloor)
      hdelta_pos htau_pos hcapacity_gap (by
        filter_upwards [htail] with C htailC _
        exact htailC)
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  filter_upwards [hcross] with C hcrossC cutoff hcard
  simpa [quantile] using
    (theorem4_floorPower_integral_gt_of_tail_crossing
      noiseLaw eta hp_pos hvalueMass hcard (hcrossC ()))

/--
The uniform floor-power certificate implies the actual iid local-affordance
integral crossing for every local cutoff vector.  This is the analytic input
consumed by the global-market coalition capacity bridge.
-/
theorem exists_theorem4_uniform_low_cutoff_integral_capacity_certificate_at_vHigh_of_longTailed
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (eta : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure eta]
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ cutoff : Fin (C + 1) → ℝ,
            epsilonFloorSplitIndex (tol / 2) C <
                (lowCutoffIndexSet cutoff
                  (vHigh + theorem4HighTailQuantile noiseLaw sigma C)).card →
              totalSupply <
                ∫ v : ℝ,
                  cutoffAffordanceProbability
                    (MeasureTheory.Measure.pi
                      (fun _ : Fin (C + 1) => noiseLaw))
                    (lowCutoffIndexSet cutoff
                      (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
                    v cutoff
                  ∂eta := by
  rcases
      exists_theorem4_uniform_floor_pow_integral_capacity_certificate_at_vHigh_of_longTailed
        noiseLaw hlong eta htol_pos htotalSupply_lt_one with
    ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, hfloor⟩
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  haveI : MeasureTheory.IsFiniteMeasure eta := by infer_instance
  filter_upwards [hfloor] with C hfloorC cutoff hcard
  have hstrict := hfloorC cutoff hcard
  simpa [cutoffAffordanceProbability] using
    (AppliedModelingLib.Matching.lt_integral_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_integral_one_sub_lowerCDFMass_pow_card
      noiseLaw eta hstrict)

end

end PG24NoisyMatchingMarkets
