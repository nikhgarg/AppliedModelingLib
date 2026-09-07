import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem4ParameterSelection
import Mathlib.Tactic

/-!
# Theorem 4 Integrated Capacity

The capacity step is proved at the population level.  A fixed lower value
anchor with enough `eta` mass turns the iid constant-cutoff crossing bound
into the required value-integrated strict inequality.  No pointwise
match-event or affordance-event bridge is used here.
-/

open Filter Topology
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u

/--
A strict crossing inequality at one value anchor yields the corresponding
value-integrated floor-power inequality whenever that anchor's upper tail has
enough mass.  This is the analytic part of the Theorem 4 low-cutoff capacity
argument.
-/
theorem theorem4_floorPower_integral_gt_of_tail_crossing
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (eta : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure eta]
    {totalSupply p floor valueFloor : ℝ} {split m : ℕ}
    (hp_pos : 0 < p)
    (hvalueMass : p ≤ eta.real (Set.Ici valueFloor))
    (hcard : split < m)
    (hcross :
      totalSupply / p <
        1 -
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (floor - valueFloor)) ^ (split + 1)) :
    totalSupply <
      ∫ v : ℝ,
        1 -
          (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v)) ^ m
        ∂eta := by
  let q : ℝ := floor - valueFloor
  let base : ℝ := AppliedModelingLib.Probability.lowerCDFMass noiseLaw q
  let crossing : ℝ := 1 - base ^ m
  have hbase_nonneg : 0 ≤ base := by
    exact AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw q
  have hbase_le_one : base ≤ 1 := by
    exact AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw q
  have hbase_pow_le_one : base ^ m ≤ 1 :=
    pow_le_one₀ hbase_nonneg hbase_le_one
  have hcross_nonneg : 0 ≤ crossing := by
    dsimp [crossing]
    linarith
  have htail_sum :=
    AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one noiseLaw q
  have hbase_eq :
      base =
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw q := by
    dsimp [base]
    linarith
  have hsplit_le : split + 1 ≤ m :=
    Nat.succ_le_of_lt hcard
  have hpow_le : base ^ m ≤ base ^ (split + 1) :=
    pow_right_anti₀ hbase_nonneg hbase_le_one hsplit_le
  have hcross_split :
      totalSupply / p < 1 - base ^ (split + 1) := by
    simpa [q, hbase_eq] using hcross
  have hcross_scaled : totalSupply / p < crossing := by
    dsimp [crossing]
    linarith
  have hscaled : totalSupply < p * crossing := by
    have h := (div_lt_iff₀ hp_pos).mp hcross_scaled
    simpa [mul_comm] using h
  let integrand : ℝ → ℝ := fun v =>
    1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v)) ^ m
  have hintegrand_integrable : MeasureTheory.Integrable integrand eta := by
    simpa [integrand] using
      (AppliedModelingLib.Matching.one_sub_lowerCDFMass_pow_integrable_value
        noiseLaw eta floor m)
  have hindicator_integrable :
      MeasureTheory.Integrable
        ((Set.Ici valueFloor).indicator (fun _ : ℝ => crossing)) eta := by
    exact (MeasureTheory.integrable_const _).indicator measurableSet_Ici
  have hpointwise :
      ∀ v : ℝ,
        (Set.Ici valueFloor).indicator (fun _ : ℝ => crossing) v ≤
          integrand v := by
    intro v
    by_cases hv : valueFloor ≤ v
    · rw [Set.indicator_of_mem]
      · have harg : floor - v ≤ q := by
          dsimp [q]
          linarith
        have hbase_v_nonneg :
            0 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v) :=
          AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _
        have hbase_v_le :
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v) ≤ base := by
          exact (AppliedModelingLib.Probability.lowerCDFMass_mono noiseLaw harg)
        have hpow_v_le :
            (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v)) ^ m ≤
              base ^ m :=
          pow_le_pow_left₀ hbase_v_nonneg hbase_v_le m
        dsimp [integrand, crossing]
        linarith
      · exact hv
    · rw [Set.indicator_of_notMem]
      · have hbase_v_nonneg :
            0 ≤ AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v) :=
          AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _
        have hbase_v_le_one :
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v) ≤ 1 :=
          AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _
        have hpow_v_le_one :
            (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v)) ^ m ≤ 1 :=
          pow_le_one₀ hbase_v_nonneg hbase_v_le_one
        dsimp [integrand]
        linarith
      · simpa only [Set.mem_Ici, not_le] using hv
  have hintegral_le :
      (∫ v : ℝ,
        (Set.Ici valueFloor).indicator (fun _ : ℝ => crossing) v ∂eta) ≤
        ∫ v : ℝ, integrand v ∂eta :=
    MeasureTheory.integral_mono hindicator_integrable hintegrand_integrable
      hpointwise
  calc
    totalSupply < p * crossing := hscaled
    _ ≤ eta.real (Set.Ici valueFloor) * crossing :=
      mul_le_mul_of_nonneg_right hvalueMass hcross_nonneg
    _ = ∫ v : ℝ,
        (Set.Ici valueFloor).indicator (fun _ : ℝ => crossing) v ∂eta := by
      simp [smul_eq_mul]
    _ ≤ ∫ v : ℝ, integrand v ∂eta := hintegral_le
    _ = ∫ v : ℝ,
        1 -
          (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - v)) ^ m
        ∂eta := by
      rfl

/--
Long-tailed iid noise, a fixed probability value law, and strict total supply
below one construct the Lemma-11-style floor-power integral capacity
certificate for the explicit Theorem 4 quantile.
-/
theorem exists_theorem4_floor_pow_integral_capacity_certificate_of_longTailed
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (eta : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure eta]
    (value_law_eq_eta :
      source_assumption_theorem4_value_law_eq_eta valueLaw eta)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply tol : ℝ}
    (htol_pos : 0 < tol)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧
        source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
          Mseq noiseLaw valueLaw cutoffOut
          (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
          (fun C (_a : Admissible C) =>
            valueFloor + theorem4HighTailQuantile noiseLaw sigma C)
          totalSupply := by
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
  rcases hvalue_tail.exists with ⟨valueFloor, hvalue_tail_floor⟩
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
  rcases exists_positive_sigma_tau_of_totalSupply_lt_one
    (delta := tol / 2) (totalSupply := totalSupply / p)
    (slack := (1 / 2 : ℝ)) hdelta_pos hscaledSupply_lt_one
    (by norm_num) with
    ⟨sigma, tau, hsigma_pos, htau_pos, htau_eq, hcapacity_gap⟩
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        (1 - (1 / 2 : ℝ)) * (sigma / (((C + 1 : ℕ) : ℝ))) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) :=
    theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_of_longTailed
      noiseLaw hlong hsigma_pos (by norm_num) (by norm_num)
  have htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          tau / (((C + 1 : ℕ) : ℝ)) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((valueFloor + theorem4HighTailQuantile noiseLaw sigma C) -
                valueFloor) := by
    filter_upwards [hquantile_tail] with C hquantile_tail_C a
    calc
      tau / (((C + 1 : ℕ) : ℝ)) =
          (1 - (1 / 2 : ℝ)) * (sigma / (((C + 1 : ℕ) : ℝ)) ) := by
        rw [htau_eq]
        ring
      _ ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) := hquantile_tail_C
      _ = AppliedModelingLib.Probability.upperTailMass noiseLaw
          ((valueFloor + theorem4HighTailQuantile noiseLaw sigma C) -
            valueFloor) := by
        congr 1
        ring
  have hcross :=
    pg24_eventually_upperTail_split_crossing_of_scalar_lower_static_gap
      (Admissible := Admissible) noiseLaw
      (delta := tol / 2) (tau := tau)
      (totalSupply := totalSupply / p)
      (lowerCutoff := fun C (_a : Admissible C) =>
        valueFloor + theorem4HighTailQuantile noiseLaw sigma C)
      (eventValue := fun _C (_a : Admissible _C) => valueFloor)
      hdelta_pos htau_pos hcapacity_gap htail
  refine ⟨sigma, valueFloor, hsigma_pos, ?_⟩
  filter_upwards [hcross] with C hcrossC a P hP hcard
  rw [value_law_eq_eta C a]
  exact
    theorem4_floorPower_integral_gt_of_tail_crossing
      noiseLaw eta hp_pos hvalueMass hcard (hcrossC a)

/--
Endpoint-preserving version of the integrated capacity certificate.  The
given `vHigh` remains the floor's high-value endpoint; a separately chosen
lower value anchor supplies the population mass used in the integral.  The
long-tail ratio transfers the quantile lower bound across that fixed shift.
-/
theorem exists_theorem4_floor_pow_integral_capacity_certificate_at_vHigh_of_longTailed
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (eta : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure eta]
    (value_law_eq_eta :
      source_assumption_theorem4_value_law_eq_eta valueLaw eta)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply tol vHigh : ℝ}
    (htol_pos : 0 < tol)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma valueFloor : ℝ,
      0 < sigma ∧ valueFloor < vHigh ∧
        source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
          Mseq noiseLaw valueLaw cutoffOut
          (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
          (fun C (_a : Admissible C) =>
            vHigh + theorem4HighTailQuantile noiseLaw sigma C)
          totalSupply := by
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
  have hquantile_upper :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw (quantile C) ≤
          sigma / (((C + 1 : ℕ) : ℝ)) := by
    simpa [quantile] using
      (theorem4HighTailQuantile_upperTailMass_le_eventually
        noiseLaw hsigma_pos)
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
        ∀ a : Admissible C,
          tau / (((C + 1 : ℕ) : ℝ)) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((vHigh + quantile C) - valueFloor) := by
    filter_upwards [hquantile_tail, hratio] with C hquantile_tail_C hratio_C a
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
      (Admissible := Admissible) noiseLaw
      (delta := tol / 2) (tau := tau)
      (totalSupply := totalSupply / p)
      (lowerCutoff := fun C (_a : Admissible C) => vHigh + quantile C)
      (eventValue := fun _C (_a : Admissible _C) => valueFloor)
      hdelta_pos htau_pos hcapacity_gap htail
  refine ⟨sigma, valueFloor, hsigma_pos, hvalueFloor_lt, ?_⟩
  filter_upwards [hcross] with C hcrossC a P hP hcard
  rw [value_law_eq_eta C a]
  simpa [quantile] using
    (theorem4_floorPower_integral_gt_of_tail_crossing
      noiseLaw eta hp_pos hvalueMass hcard (hcrossC a))

end PG24NoisyMatchingMarkets
