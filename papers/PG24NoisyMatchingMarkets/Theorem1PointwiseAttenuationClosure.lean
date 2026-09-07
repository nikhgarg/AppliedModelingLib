import PG24NoisyMatchingMarkets.Theorem1LiteralLargeGapConclusion
import PG24NoisyMatchingMarkets.Theorem2HolderNoAtoms
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

/-!
# PG24 Theorem 1 pointwise attenuation closure

This module turns the repaired qualitative tail-mass conclusion into the
fixed-value conclusion of the source theorem.  The interval mass used in that
step is derived from the stated connected-support, Holder-regular value law;
it is not supplied as a tail-proof convenience.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
The source value-law assumptions put positive value mass strictly between any
fixed value below the supply threshold and the threshold itself.
-/
theorem theorem1_low_interval_mass_pos_of_connected_support
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    {totalSupply vS v : ℝ}
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hv : v < vS) :
    0 < eta.real (Set.Ioo v vS) := by
  letI : NoAtoms eta := hregular.noAtoms
  have hhigh_real_pos : 0 < eta.real (Set.Ioi vS) := by
    rw [htail_normalization]
    exact htotalSupply_pos
  have hlow_real_eq : eta.real (Set.Iio vS) = 1 - totalSupply := by
    have hcompl := MeasureTheory.probReal_compl_eq_one_sub
      (μ := eta) (s := Set.Iic vS) measurableSet_Iic
    have hIic_compl : (Set.Iic vS)ᶜ = Set.Ioi vS := by
      ext x
      simp
    rw [hIic_compl, htail_normalization] at hcompl
    calc
      eta.real (Set.Iio vS) = eta.real (Set.Iic vS) :=
        MeasureTheory.measureReal_congr (MeasureTheory.Iio_ae_eq_Iic (μ := eta))
      _ = 1 - totalSupply := by linarith
  have hlow_real_pos : 0 < eta.real (Set.Iio vS) := by
    rw [hlow_real_eq]
    linarith
  have hhigh_pos : 0 < eta (Set.Ioi vS) :=
    (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
  have hlow_pos : 0 < eta (Set.Iio vS) :=
    (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
  rcases MeasureTheory.Measure.nonempty_inter_support_of_pos hlow_pos with
    ⟨a, ha_low, ha_support⟩
  rcases MeasureTheory.Measure.nonempty_inter_support_of_pos hhigh_pos with
    ⟨b, hb_high, hb_support⟩
  have hsupport_interval : ∃ w ∈ Set.Ioo v vS, w ∈ eta.support := by
    by_cases hva : v < a
    · exact ⟨a, ⟨hva, ha_low⟩, ha_support⟩
    · have hav : a ≤ v := le_of_not_gt hva
      let w : ℝ := (v + vS) / 2
      have hvw : v < w := by
        dsimp [w]
        linarith
      have hwvS : w < vS := by
        dsimp [w]
        linarith
      have haw : a ≤ w := le_trans hav (le_of_lt hvw)
      have hwb : w ≤ b := le_trans (le_of_lt hwvS) (le_of_lt hb_high)
      exact ⟨w, ⟨hvw, hwvS⟩,
        hconnected.Icc_subset ha_support hb_support ⟨haw, hwb⟩⟩
  rcases hsupport_interval with ⟨w, hw_interval, hw_support⟩
  have hmeasure_pos : 0 < eta (Set.Ioo v vS) :=
    (MeasureTheory.Measure.mem_support_iff_forall w).mp hw_support
      (Set.Ioo v vS) (Ioo_mem_nhds hw_interval.1 hw_interval.2)
  exact ENNReal.toReal_pos hmeasure_pos.ne' (measure_ne_top eta _)

/--
The symmetric source value-law fact above the supply threshold.
-/
theorem theorem1_high_interval_mass_pos_of_connected_support
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    {totalSupply vS v : ℝ}
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hv : vS < v) :
    0 < eta.real (Set.Ioo vS v) := by
  letI : NoAtoms eta := hregular.noAtoms
  have hhigh_real_pos : 0 < eta.real (Set.Ioi vS) := by
    rw [htail_normalization]
    exact htotalSupply_pos
  have hlow_real_eq : eta.real (Set.Iio vS) = 1 - totalSupply := by
    have hcompl := MeasureTheory.probReal_compl_eq_one_sub
      (μ := eta) (s := Set.Iic vS) measurableSet_Iic
    have hIic_compl : (Set.Iic vS)ᶜ = Set.Ioi vS := by
      ext x
      simp
    rw [hIic_compl, htail_normalization] at hcompl
    calc
      eta.real (Set.Iio vS) = eta.real (Set.Iic vS) :=
        MeasureTheory.measureReal_congr (MeasureTheory.Iio_ae_eq_Iic (μ := eta))
      _ = 1 - totalSupply := by linarith
  have hlow_real_pos : 0 < eta.real (Set.Iio vS) := by
    rw [hlow_real_eq]
    linarith
  have hhigh_pos : 0 < eta (Set.Ioi vS) :=
    (ENNReal.toReal_pos_iff.mp hhigh_real_pos).1
  have hlow_pos : 0 < eta (Set.Iio vS) :=
    (ENNReal.toReal_pos_iff.mp hlow_real_pos).1
  rcases MeasureTheory.Measure.nonempty_inter_support_of_pos hlow_pos with
    ⟨a, ha_low, ha_support⟩
  rcases MeasureTheory.Measure.nonempty_inter_support_of_pos hhigh_pos with
    ⟨b, hb_high, hb_support⟩
  have hsupport_interval : ∃ w ∈ Set.Ioo vS v, w ∈ eta.support := by
    by_cases hbv : b < v
    · exact ⟨b, ⟨hb_high, hbv⟩, hb_support⟩
    · have hvb : v ≤ b := le_of_not_gt hbv
      let w : ℝ := (vS + v) / 2
      have hvSw : vS < w := by
        dsimp [w]
        linarith
      have hwv : w < v := by
        dsimp [w]
        linarith
      have haw : a ≤ w := le_trans (le_of_lt ha_low) (le_of_lt hvSw)
      have hwb : w ≤ b := le_trans (le_of_lt hwv) hvb
      exact ⟨w, ⟨hvSw, hwv⟩,
        hconnected.Icc_subset ha_support hb_support ⟨haw, hwb⟩⟩
  rcases hsupport_interval with ⟨w, hw_interval, hw_support⟩
  have hmeasure_pos : 0 < eta (Set.Ioo vS v) :=
    (MeasureTheory.Measure.mem_support_iff_forall w).mp hw_support
      (Set.Ioo vS v) (Ioo_mem_nhds hw_interval.1 hw_interval.2)
  exact ENNReal.toReal_pos hmeasure_pos.ne' (measure_ne_top eta _)

/--
Monotonicity of literal cutoff affordability turns a fixed low-value
probability into a lower bound on the low-value affordance integral.
-/
theorem theorem1_low_affordance_interval_mass_mul_le_low_integral
    {n : ℕ} (eta noiseLaw : Measure ℝ)
    [IsProbabilityMeasure eta] [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ) {v vS : ℝ} (hv : v < vS) :
    eta.real (Set.Ioo v vS) *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v cutoff ≤
      ∫ value : ℝ,
        (Set.Iic vS).indicator
          (fun value => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) value cutoff) value
        ∂eta := by
  let productLaw : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  let p : ℝ → ℝ := fun value =>
    cutoffAffordanceProbability productLaw
      (Finset.univ : Finset (Fin n)) value cutoff
  have hp_integrable : Integrable p eta := by
    simpa [p, productLaw, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw eta (Finset.univ : Finset (Fin n)) cutoff)
  have hindicator_integrable : Integrable ((Set.Iic vS).indicator p) eta :=
    hp_integrable.indicator measurableSet_Iic
  have hlow : ∀ value ∈ Set.Ioo v vS,
      p v ≤ (Set.Iic vS).indicator p value := by
    intro value hvalue
    have hmem : value ∈ Set.Iic vS := le_of_lt hvalue.2
    simpa only [Set.indicator_of_mem hmem] using
      (cutoffAffordanceProbability_mono_value productLaw
        (show v ≤ value from le_of_lt hvalue.1))
  have hnonneg : ∀ value ∉ Set.Ioo v vS,
      0 ≤ (Set.Iic vS).indicator p value := by
    intro value _
    by_cases hvalue : value ∈ Set.Iic vS
    · rw [Set.indicator_of_mem hvalue]
      exact cutoffAffordanceProbability_nonneg productLaw
        (Finset.univ : Finset (Fin n)) value cutoff
    · rw [Set.indicator_of_notMem hvalue]
  have hbound := AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
    eta measurableSet_Ioo hindicator_integrable hlow hnonneg
  simpa [p, productLaw, mul_comm] using hbound

/--
The symmetric lower bound for unmatched probability above the threshold.
-/
theorem theorem1_high_unaffordance_interval_mass_mul_le_high_integral
    {n : ℕ} (eta noiseLaw : Measure ℝ)
    [IsProbabilityMeasure eta] [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin n → ℝ) {vS v : ℝ} (hv : vS < v) :
    eta.real (Set.Ioo vS v) *
        (1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw))
          (Finset.univ : Finset (Fin n)) v cutoff) ≤
      ∫ value : ℝ,
        (Set.Ioi vS).indicator
          (fun value => 1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw))
            (Finset.univ : Finset (Fin n)) value cutoff) value
        ∂eta := by
  let productLaw : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => noiseLaw)
  let p : ℝ → ℝ := fun value =>
    cutoffAffordanceProbability productLaw
      (Finset.univ : Finset (Fin n)) value cutoff
  let failure : ℝ → ℝ := fun value => 1 - p value
  have hp_integrable : Integrable p eta := by
    simpa [p, productLaw, cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
        productLaw eta (Finset.univ : Finset (Fin n)) cutoff)
  have hfailure_integrable : Integrable failure eta :=
    (integrable_const _).sub hp_integrable
  have hindicator_integrable : Integrable ((Set.Ioi vS).indicator failure) eta :=
    hfailure_integrable.indicator measurableSet_Ioi
  have hlow : ∀ value ∈ Set.Ioo vS v,
      failure v ≤ (Set.Ioi vS).indicator failure value := by
    intro value hvalue
    have hmem : value ∈ Set.Ioi vS := hvalue.1
    rw [Set.indicator_of_mem hmem]
    have hp_mono : p value ≤ p v :=
      cutoffAffordanceProbability_mono_value productLaw
        (show value ≤ v from le_of_lt hvalue.2)
    dsimp [failure]
    linarith
  have hnonneg : ∀ value ∉ Set.Ioo vS v,
      0 ≤ (Set.Ioi vS).indicator failure value := by
    intro value _
    by_cases hvalue : value ∈ Set.Ioi vS
    · rw [Set.indicator_of_mem hvalue]
      dsimp [failure, p]
      linarith [cutoffAffordanceProbability_le_one productLaw
        (Finset.univ : Finset (Fin n)) value cutoff]
    · rw [Set.indicator_of_notMem hvalue]
  have hbound := AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
    eta measurableSet_Ioo hindicator_integrable hlow hnonneg
  simpa [failure, p, productLaw, mul_comm] using hbound

/--
A qualitative vanishing low-value affordance integral gives pointwise
attenuation at every fixed value with positive intervening value-law mass.
-/
theorem theorem1_low_pointwise_tendsto_zero_of_low_integral
    (eta noiseLaw : Measure ℝ)
    [IsProbabilityMeasure eta] [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ} {v vS : ℝ}
    (hv : v < vS) (hinterval : 0 < eta.real (Set.Ioo v vS))
    (hlow_integral : Tendsto (fun C : ℕ =>
      ∫ value : ℝ,
        (Set.Iic vS).indicator
          (fun value => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)) value
        ∂eta) atTop (nhds 0)) :
    Tendsto (fun C : ℕ => cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)) atTop (nhds 0) := by
  let p : ℕ → ℝ := fun C => cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
    (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)
  let lowIntegral : ℕ → ℝ := fun C =>
    ∫ value : ℝ,
      (Set.Iic vS).indicator
        (fun value => cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)) value
      ∂eta
  have hbound : ∀ C : ℕ, eta.real (Set.Ioo v vS) * p C ≤ lowIntegral C := by
    intro C
    simpa [p, lowIntegral] using
      (theorem1_low_affordance_interval_mass_mul_le_low_integral
        eta noiseLaw (cutoff C) hv)
  have hupper : ∀ C : ℕ, p C ≤ lowIntegral C / eta.real (Set.Ioo v vS) := by
    intro C
    exact (le_div_iff₀ hinterval).mpr (by simpa [mul_comm] using hbound C)
  have hupper_tendsto : Tendsto
      (fun C : ℕ => lowIntegral C / eta.real (Set.Ioo v vS))
      atTop (nhds 0) := by
    simpa using
      (hlow_integral.div tendsto_const_nhds (ne_of_gt hinterval))
  have hnonneg : ∀ C : ℕ, 0 ≤ p C := by
    intro C
    exact cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)
  simpa [p] using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper_tendsto (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hupper))

/--
The symmetric qualitative closure: vanishing unmatched mass above the
threshold makes the fixed-value match probability tend to one.
-/
theorem theorem1_high_pointwise_tendsto_one_of_high_unmatched_integral
    (eta noiseLaw : Measure ℝ)
    [IsProbabilityMeasure eta] [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ} {vS v : ℝ}
    (hv : vS < v) (hinterval : 0 < eta.real (Set.Ioo vS v))
    (hhigh_integral : Tendsto (fun C : ℕ =>
      ∫ value : ℝ,
        (Set.Ioi vS).indicator
          (fun value => 1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)) value
        ∂eta) atTop (nhds 0)) :
    Tendsto (fun C : ℕ => cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)) atTop (nhds 1) := by
  let failure : ℕ → ℝ := fun C => 1 - cutoffAffordanceProbability
    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
    (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)
  let highIntegral : ℕ → ℝ := fun C =>
    ∫ value : ℝ,
      (Set.Ioi vS).indicator
        (fun value => 1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)) value
      ∂eta
  have hbound : ∀ C : ℕ,
      eta.real (Set.Ioo vS v) * failure C ≤ highIntegral C := by
    intro C
    simpa [failure, highIntegral] using
      (theorem1_high_unaffordance_interval_mass_mul_le_high_integral
        eta noiseLaw (cutoff C) hv)
  have hupper : ∀ C : ℕ,
      failure C ≤ highIntegral C / eta.real (Set.Ioo vS v) := by
    intro C
    exact (le_div_iff₀ hinterval).mpr (by simpa [mul_comm] using hbound C)
  have hupper_tendsto : Tendsto
      (fun C : ℕ => highIntegral C / eta.real (Set.Ioo vS v))
      atTop (nhds 0) := by
    simpa using
      (hhigh_integral.div tendsto_const_nhds (ne_of_gt hinterval))
  have hnonneg : ∀ C : ℕ, 0 ≤ failure C := by
    intro C
    dsimp [failure]
    linarith [cutoffAffordanceProbability_le_one
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) v (cutoff C)]
  have hfailure_tendsto : Tendsto failure atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper_tendsto (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hupper)
  simpa [failure] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
      hfailure_tendsto)

/--
Literal Case 2 low-side closure at one fixed value.  The interval mass is
derived from the source value law, and the low integral is the checked literal
selected-demand mass rather than an abstract tail-mass input.
-/
theorem theorem1_literal_selected_largeGap_low_pointwise_tendsto_zero
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta gamma vS totalSupply value : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)))
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hvalue : value < vS) :
    Tendsto (fun C : ℕ => cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) value
      (inst C).selectedCutoffVector) atTop (nhds 0) := by
  letI : IsProbabilityMeasure (inst 0).studentLaw :=
    (inst 0).studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← (inst 0).value_marginal]
    exact Measure.isProbabilityMeasure_map
      (inst 0).value_measurable.aemeasurable
  have hmatched :=
    theorem1_literal_selected_largeGap_low_matched_mass_tendsto_zero
      noiseLaw eta inst hbeta hgamma hvariance halpha_nonneg
      htail_normalization hlarge_gap
  have hlow_integral : Tendsto (fun C : ℕ =>
      ∫ w : ℝ,
        (Set.Iic vS).indicator
          (fun w => cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) w
            (inst C).selectedCutoffVector) w
        ∂eta) atTop (nhds 0) := by
    refine hmatched.congr fun C => ?_
    letI : IsProbabilityMeasure (inst C).studentLaw :=
      (inst C).studentLaw_isProbability
    exact theorem1_sourceDemand_value_restricted_matched_mass_eq_integral_affordance_iid
      (inst C).studentLaw (inst C).value (inst C).value_measurable eta
      (inst C).value_marginal noiseLaw (inst C).selectedCutoffVector
      ((inst C).literal.demand.demandAt (inst C).literal.selectedCutoff)
      (inst C).selected_demand_none_iff_no_crossed
      (inst C).selected_demand_feasible measurableSet_Iic
  exact theorem1_low_pointwise_tendsto_zero_of_low_integral
    eta noiseLaw hvalue
    (theorem1_low_interval_mass_pos_of_connected_support eta hconnected hregular
      htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue)
    hlow_integral

/--
Literal Case 2 high-side closure at one fixed value.  The high unmatched
integral is obtained by literal clearing conservation and literal source
demand semantics.
-/
theorem theorem1_literal_selected_largeGap_high_pointwise_tendsto_one
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta gamma vS totalSupply value : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)))
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hvalue : vS < value) :
    Tendsto (fun C : ℕ => cutoffAffordanceProbability
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (Finset.univ : Finset (Fin (C + 1))) value
      (inst C).selectedCutoffVector) atTop (nhds 1) := by
  letI : IsProbabilityMeasure (inst 0).studentLaw :=
    (inst 0).studentLaw_isProbability
  letI : IsProbabilityMeasure eta := by
    rw [← (inst 0).value_marginal]
    exact Measure.isProbabilityMeasure_map
      (inst 0).value_measurable.aemeasurable
  have hmatched :=
    theorem1_literal_selected_largeGap_low_matched_mass_tendsto_zero
      noiseLaw eta inst hbeta hgamma hvariance halpha_nonneg
      htail_normalization hlarge_gap
  have hhigh_integral : Tendsto (fun C : ℕ =>
      ∫ w : ℝ,
        (Set.Ioi vS).indicator
          (fun w => 1 - cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) w
            (inst C).selectedCutoffVector) w
        ∂eta) atTop (nhds 0) := by
    refine hmatched.congr fun C => ?_
    letI : IsProbabilityMeasure (inst C).studentLaw :=
      (inst C).studentLaw_isProbability
    calc
      eventMass
          ((inst C).studentLaw.prod
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
          (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
            (inst C).value outcome.1 ∈ Set.Iic vS ∧
              chosenInActive
                ((inst C).literal.demand.demandAt
                  (inst C).literal.selectedCutoff)
                (Finset.univ : Finset (Fin (C + 1))) outcome) =
          eventMass
            ((inst C).studentLaw.prod
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
            (fun outcome : StudentType × (Fin (C + 1) → ℝ) =>
              (inst C).value outcome.1 ∈ Set.Ioi vS ∧
                ¬ chosenInActive
                  ((inst C).literal.demand.demandAt
                    (inst C).literal.selectedCutoff)
                  (Finset.univ : Finset (Fin (C + 1))) outcome) :=
        (inst C).theorem1_selected_low_matched_mass_eq_high_unmatched_mass
          vS htail_normalization
      _ = ∫ w : ℝ,
          (Set.Ioi vS).indicator
            (fun w => 1 - cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) w
              (inst C).selectedCutoffVector) w
          ∂eta := by
        exact theorem1_source_model_value_restricted_unmatched_mass_eq_integral_affordance_complement
          (inst C).studentLaw (inst C).value (inst C).value_measurable eta
          (inst C).value_marginal
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (inst C).selectedCutoffVector
          ((inst C).literal.demand.demandAt (inst C).literal.selectedCutoff)
          (inst C).theorem1_selected_chosenInAll_iff_affordance
          measurableSet_Ioi
  exact theorem1_high_pointwise_tendsto_one_of_high_unmatched_integral
    eta noiseLaw hvalue
    (theorem1_high_interval_mass_pos_of_connected_support eta hconnected hregular
      htotalSupply_pos htotalSupply_lt_one htail_normalization hvalue)
    hhigh_integral

/--
The literal selected-cutoff Case 2 route satisfies the source attenuation
conclusion: every fixed value below the supply threshold has vanishing
affordance probability, while every fixed value above it has probability
tending to one.
-/
theorem theorem1_literal_selected_largeGap_attenuationConclusion
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {alpha beta gamma vS totalSupply : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hgamma : 0 < gamma)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply)
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma)
            (theorem1TailPhi3 beta gamma) : ℝ) *
            Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector
          (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)))
    (hconnected : IsPreconnected eta.support)
    (hregular : PG24HolderIntervalRegular eta)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    theorem1_attenuationConclusion
      (fun C : ℕ => fun value : ℝ => cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) value
        (inst C).selectedCutoffVector)
      vS := by
  constructor
  · intro value hvalue
    exact theorem1_literal_selected_largeGap_low_pointwise_tendsto_zero
      noiseLaw eta inst hbeta hgamma hvariance halpha_nonneg
      htail_normalization hlarge_gap hconnected hregular
      htotalSupply_pos htotalSupply_lt_one hvalue
  · intro value hvalue
    exact theorem1_literal_selected_largeGap_high_pointwise_tendsto_one
      noiseLaw eta inst hbeta hgamma hvariance halpha_nonneg
      htail_normalization hlarge_gap hconnected hregular
      htotalSupply_pos htotalSupply_lt_one hvalue

end

end PG24NoisyMatchingMarkets
