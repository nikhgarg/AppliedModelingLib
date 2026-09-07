import PG24NoisyMatchingMarkets.Theorem2UniformLiteralBasic
import Mathlib.Tactic

/-!
# PG24 Theorem 2 all-real target closure

The appendix's quantile window directly covers support-interior values.  This
module supplies the missing out-of-support transfer.  A fixed positive value
shift changes a long-tailed upper tail by at most a finite global multiplier;
the multiplier controls the small cutoff block, while the existing eventual
ratio estimate controls the semantic non-low block.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w

/-- Independent at-least-one probability scales by the same factor as its
pointwise probabilities when the larger probabilities also dominate the
smaller ones. -/
theorem independentAffordanceProbability_le_mul_of_pointwise_sandwich
    {College : Type u} (active : Finset College)
    {qLow qHigh : College → ℝ} {K : ℝ}
    (hK : 1 ≤ K)
    (hlow_nonneg : ∀ c ∈ active, 0 ≤ qLow c)
    (hpointwise : ∀ c ∈ active, qLow c ≤ qHigh c)
    (hhigh_le_one : ∀ c ∈ active, qHigh c ≤ 1)
    (hscale : ∀ c ∈ active, qHigh c ≤ K * qLow c) :
    independentAffordanceProbability active qHigh ≤
      K * independentAffordanceProbability active qLow := by
  classical
  induction active using Finset.induction_on with
  | empty => simp [independentAffordanceProbability]
  | @insert c active hc ih =>
      have hlow_nonneg_c : 0 ≤ qLow c := hlow_nonneg c (by simp)
      have hpointwise_c : qLow c ≤ qHigh c := hpointwise c (by simp)
      have hhigh_le_one_c : qHigh c ≤ 1 := hhigh_le_one c (by simp)
      have hscale_c : qHigh c ≤ K * qLow c := hscale c (by simp)
      have ih' :
          independentAffordanceProbability active qHigh ≤
            K * independentAffordanceProbability active qLow :=
        ih (fun d hd => hlow_nonneg d (by simp [hd]))
          (fun d hd => hpointwise d (by simp [hd]))
          (fun d hd => hhigh_le_one d (by simp [hd]))
          (fun d hd => hscale d (by simp [hd]))
      have hmono :
          independentAffordanceProbability active qLow ≤
            independentAffordanceProbability active qHigh :=
        independentAffordanceProbability_mono_of_pointwise_le active
          (fun d hd => hpointwise d (by simp [hd]))
          (fun d hd => hhigh_le_one d (by simp [hd]))
      have hhigh_prob_le_one :
          independentAffordanceProbability active qHigh ≤ 1 := by
        have hprod_nonneg :
            0 ≤ ∏ d ∈ active, (1 - qHigh d) :=
          Finset.prod_nonneg (fun d hd => by
            linarith [hhigh_le_one d (by simp [hd])])
        unfold independentAffordanceProbability
        linarith
      have hK_nonneg : 0 ≤ K := le_trans (by norm_num) hK
      have hqHigh_nonneg : 0 ≤ qHigh c :=
        hlow_nonneg_c.trans hpointwise_c
      have hresidual_nonneg :
          0 ≤ 1 - independentAffordanceProbability active qHigh := by
        linarith
      have hresidual_le :
          1 - independentAffordanceProbability active qHigh ≤
            1 - independentAffordanceProbability active qLow := by
        linarith
      have hinsert (q : College → ℝ) :
          independentAffordanceProbability (insert c active) q =
            independentAffordanceProbability active q +
              q c * (1 - independentAffordanceProbability active q) := by
        simp [independentAffordanceProbability, hc]
        ring
      rw [hinsert qHigh, hinsert qLow]
      calc
        independentAffordanceProbability active qHigh +
              qHigh c * (1 - independentAffordanceProbability active qHigh) ≤
            K * independentAffordanceProbability active qLow +
              (K * qLow c) *
                (1 - independentAffordanceProbability active qHigh) :=
          add_le_add ih'
            (mul_le_mul_of_nonneg_right hscale_c hresidual_nonneg)
        _ ≤ K * independentAffordanceProbability active qLow +
              (K * qLow c) *
                (1 - independentAffordanceProbability active qLow) := by
          gcongr
        _ = K * (independentAffordanceProbability active qLow +
              qLow c * (1 - independentAffordanceProbability active qLow)) := by
          ring

/-- For two fixed values, a long-tailed upper tail has a finite global
high-value/low-value multiplier.  Eventual ratio convergence handles high
cutoffs; antitonicity and eventual positivity handle the bounded remainder. -/
theorem exists_upperTailMass_value_multiplier_of_longTailed
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {vLow vHigh : ℝ} (hv : vLow ≤ vHigh) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ cutoff : ℝ,
      AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - vHigh) ≤
        K * AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - vLow) := by
  rcases hv.eq_or_lt with rfl | hvStrict
  · refine ⟨1, le_rfl, ?_⟩
    intro cutoff
    simp
  · let survival := AppliedModelingLib.Probability.upperTailMass noiseLaw
    let d := vHigh - vLow
    have hd : 0 < d := by
      dsimp [d]
      linarith
    have hratio :
        ∀ᶠ x : ℝ in atTop,
          (1 / 2 : ℝ) < survival (x + d) / survival x :=
      by
        filter_upwards
          [hlong.eventually_ratio_gt (d := d) (ε := (1 / 2 : ℝ)) hd (by norm_num)]
          with x hx
        norm_num at hx
        simpa [survival] using hx
    have hpositive : ∀ᶠ x : ℝ in atTop, 0 < survival x :=
      hlong.eventually_pos
        (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x)
    rcases Filter.eventually_atTop.1 (hratio.and hpositive) with
      ⟨x0, hx0⟩
    have hx0_data := hx0 x0 le_rfl
    have hbase_pos : 0 < survival (x0 + d) := by
      have hmul := (lt_div_iff₀ hx0_data.2).mp hx0_data.1
      nlinarith
    let K : ℝ := max 2 (1 / survival (x0 + d))
    refine ⟨K, le_trans (by norm_num) (le_max_left _ _), ?_⟩
    intro cutoff
    let x := cutoff - vHigh
    have hrewrite : x + d = cutoff - vLow := by
      dsimp [x, d]
      ring
    by_cases hx : x0 ≤ x
    · have hx_data := hx0 x hx
      have hmul := (lt_div_iff₀ hx_data.2).mp hx_data.1
      have htwo : survival x ≤ 2 * survival (x + d) := by
        nlinarith
      calc
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - vHigh) =
            survival x := rfl
        _ ≤ 2 * survival (x + d) := htwo
        _ ≤ K * survival (x + d) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _)
        _ = K * AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff - vLow) := by rw [hrewrite]
    · have hxle : x + d ≤ x0 + d := by
        linarith [le_of_not_ge hx]
      have hbase_le : survival (x0 + d) ≤ survival (x + d) :=
        AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw hxle
      have hone : 1 ≤ (1 / survival (x0 + d)) * survival (x + d) := by
        calc
          1 = (1 / survival (x0 + d)) * survival (x0 + d) := by
            field_simp [ne_of_gt hbase_pos]
          _ ≤ (1 / survival (x0 + d)) * survival (x + d) :=
            mul_le_mul_of_nonneg_left hbase_le (by positivity)
      calc
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff - vHigh) ≤ 1 :=
          AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _
        _ ≤ (1 / survival (x0 + d)) * survival (x + d) := hone
        _ ≤ K * survival (x + d) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _)
        _ = K * AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff - vLow) := by rw [hrewrite]

/-- The global single-college multiplier transports to every finite iid
affordance block. -/
theorem exists_cutoffAffordanceProbability_value_multiplier_of_longTailed
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {vLow vHigh : ℝ} (hv : vLow ≤ vHigh) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (n : ℕ) (active : Finset (Fin n)) (cutoff : Fin n → ℝ),
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) active vHigh cutoff ≤
          K * cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) active vLow cutoff := by
  rcases exists_upperTailMass_value_multiplier_of_longTailed
      noiseLaw hlong hv with ⟨K, hK, hscale⟩
  refine ⟨K, hK, ?_⟩
  intro n active cutoff
  rw [cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass,
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass]
  apply independentAffordanceProbability_le_mul_of_pointwise_sandwich
    active hK
  · intro c hc
    exact AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
  · intro c hc
    exact AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw (by linarith)
  · intro c hc
    exact AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _
  · intro c hc
    exact hscale (cutoff c)

/-- Holder regularity gives at least one value with positive mass on both
sides.  This anchor is used only to organize the out-of-support case split. -/
theorem exists_supportInterior_anchor_of_holder
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hregular : PG24HolderIntervalRegular eta) :
    ∃ anchor : ℝ,
      0 < eta.real (Set.Iio anchor) ∧
      0 < eta.real (Set.Ioi anchor) := by
  letI : NoAtoms eta := hregular.noAtoms
  have hepsilon_pos : 0 < (1 / 16 : ℝ) := by norm_num
  have hquantile : Real.sqrt (1 / 16 : ℝ) + (1 / 16 : ℝ) / 2 < 1 := by
    rw [show Real.sqrt (1 / 16 : ℝ) = 1 / 4 by norm_num]
    norm_num
  rcases theorem2_exists_exactQuantileWindow_of_noAtoms
      eta hepsilon_pos hquantile with
    ⟨vLow, vHigh, vStar, hwindow⟩
  refine ⟨vHigh, ?_, ?_⟩
  · have hsum := AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one
      eta vHigh
    have htail : AppliedModelingLib.Probability.upperTailMass eta vHigh = 1 / 32 := by
      rw [hwindow.upper_tail]
      norm_num
    have hlower : AppliedModelingLib.Probability.lowerCDFMass eta vHigh = 31 / 32 := by
      linarith
    rw [theorem2_real_Iio_eq_lowerCDFMass_of_noAtoms eta vHigh, hlower]
    norm_num
  · simpa [AppliedModelingLib.Probability.upperTailMass] using
      (show 0 < AppliedModelingLib.Probability.upperTailMass eta vHigh by
        rw [hwindow.upper_tail]
        norm_num)

namespace PG24LiteralBasicTwoScaleInstance

/-- The fixed-market two-scale closure above the quantile anchor.  The
long-tail multiplier is used only for the low-cutoff block; the large block
continues to use the source capacity and clearing arguments. -/
theorem theorem2_twoScaleRegularWindow_of_literalBasic_highTarget
    {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type w}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
      StudentType Cutoff)
    (small large : Finset (Fin (C + 1)))
    (hdisjoint : Disjoint small large)
    (hcover : small ∪ large = (Finset.univ : Finset (Fin (C + 1))))
    {largeRegion smallRegion : Set ℝ}
    {delta endpoint sigma vLow vHigh vStar anchor target K : ℝ}
    (hlargeRegion_meas : MeasurableSet largeRegion)
    (hlargeRegion_mass : 1 - delta ≤ eta.real largeRegion)
    (hlargeRegion_ge : ∀ value : ℝ, value ∈ largeRegion → vLow ≤ value)
    (hlargeRegion_le_high :
      ∀ value : ℝ, value ∈ largeRegion → value ≤ vHigh)
    (hsmallRegion_meas : MeasurableSet smallRegion)
    (hsmallRegion_mass : Real.sqrt delta ≤ eta.real smallRegion)
    (hsmallRegion_ge : ∀ value : ℝ, value ∈ smallRegion → vStar ≤ value)
    (hsmallRegion_le_high :
      ∀ value : ℝ, value ∈ smallRegion → value ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_delta_lt_one : totalSupply + delta < 1)
    (hdenom_nonneg :
      0 ≤ theorem2_twoScaleDenominator totalSupply delta endpoint sigma)
    (hendpoint_nonneg : 0 ≤ endpoint) (hsigma_nonneg : 0 ≤ sigma)
    (hv_low : vLow ≤ target) (hv_high : target ≤ vHigh)
    (hanchor_star : anchor ≤ vStar)
    (hfailure_ratio :
      ∀ c ∈ large,
        Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (inst.selectedCutoffVector c - vHigh)) /
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (inst.selectedCutoffVector c - vLow)))
    (hlow_failure_pos :
      ∀ c ∈ large,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow))
    (hlow_failure_le_one :
      ∀ c ∈ large,
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (inst.selectedCutoffVector c - vLow) ≤ 1)
    (hsmall_card : (small.card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ))
    (hK : 1 ≤ K)
    (hsmall_scale :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small target
          inst.selectedCutoffVector ≤
        K * cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small anchor
          inst.selectedCutoffVector)
    (halpha_nonneg : 0 ≤ alpha)
    (hden_pos :
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :
    theorem2TwoScaleRegularWindow totalSupply (K * alpha) delta endpoint sigma
      (cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) target
        inst.selectedCutoffVector) := by
  letI : IsProbabilityMeasure inst.studentLaw := inst.studentLaw_isProbability
  have hn_pos : 0 < ((C + 1 : ℕ) : ℝ) := by positivity
  have hlarge_high_lower :
      totalSupply - (1 + alpha) * delta ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) large vHigh
          inst.selectedCutoffVector :=
    theorem2_sourceModel_largeHigh_lower_of_capacityRegular
      inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
      noiseLaw small large hdisjoint hcover inst.selectedCutoffVector
      hlargeRegion_meas hlargeRegion_mass hlargeRegion_le_high
      (inst.literal.demand.demandAt inst.literal.selectedCutoff)
      inst.selected_demand_feasible
      (inst.literal.demand.aggregateDemand inst.literal.selectedCutoff)
      inst.literal.capacity (inst.selected_choiceMass_eq_aggregateDemand large)
      inst.selected_clearing inst.literal.totalCapacity_eq hsmall_card
      halpha_nonneg hn_pos inst.capacity_regular
  have hK_nonneg : 0 ≤ K := le_trans (by norm_num) hK
  have hKalpha : alpha ≤ K * alpha := by nlinarith
  have hcoefficient : 1 + alpha ≤ 1 + K * alpha := by linarith
  have hscaled_coefficient :
      (1 + alpha) * delta ≤ (1 + K * alpha) * delta :=
    mul_le_mul_of_nonneg_right hcoefficient hdelta_pos.le
  have hlarge_high_lower_scaled :
      totalSupply - (1 + K * alpha) * delta ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) large vHigh
          inst.selectedCutoffVector := by
    linarith
  have hlarge_endpoint_gap :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) large vHigh
          inst.selectedCutoffVector -
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) large vLow
          inst.selectedCutoffVector ≤
        theorem2_twoScaleProductGap endpoint sigma :=
    theorem2_twoScale_iidLargeEndpointGap_of_failureRatio
      noiseLaw large inst.selectedCutoffVector hendpoint_nonneg hsigma_nonneg
      hn_pos hfailure_ratio hlow_failure_pos hlow_failure_le_one
  have hlarge_residual :
      theorem2_twoScaleDenominator totalSupply delta endpoint sigma ≤
        1 - cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) large target
          inst.selectedCutoffVector :=
    theorem2_twoScale_residual_of_sourceModel_globalClearing_and_failureRatio
      inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
      noiseLaw large inst.selectedCutoffVector hlargeRegion_meas
      hlargeRegion_mass hlargeRegion_ge hdelta_pos htotalSupply_nonneg
      htotalSupply_delta_lt_one hv_high hendpoint_nonneg hsigma_nonneg hn_pos
      hfailure_ratio hlow_failure_pos hlow_failure_le_one
      (inst.literal.demand.demandAt inst.literal.selectedCutoff)
      inst.selected_demand_none_iff_no_crossed
      (inst.literal.demand.aggregateDemand inst.literal.selectedCutoff)
      inst.literal.capacity (inst.selected_choiceMass_eq_aggregateDemand Finset.univ)
      inst.selected_clearing inst.literal.totalCapacity_eq
  have hsmall_at_star :
      theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
        (cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small vStar
          inst.selectedCutoffVector) :=
    theorem2_twoScaleSmallFirmSourceBound_of_sourceModel_regional_capacityRegular
      inst.studentLaw inst.value inst.value_measurable eta inst.value_marginal
      noiseLaw small large hdisjoint hcover inst.selectedCutoffVector
      hlargeRegion_meas hlargeRegion_mass hlargeRegion_ge hsmallRegion_meas
      hsmallRegion_mass hsmallRegion_ge hsmallRegion_le_high hdelta_pos
      htotalSupply_nonneg htotalSupply_delta_lt_one hdenom_nonneg
      hendpoint_nonneg hsigma_nonneg hn_pos hfailure_ratio hlow_failure_pos
      hlow_failure_le_one
      (inst.literal.demand.demandAt inst.literal.selectedCutoff)
      inst.selected_demand_none_iff_no_crossed inst.selected_demand_feasible
      (inst.literal.demand.aggregateDemand inst.literal.selectedCutoff)
      inst.literal.capacity (inst.selected_choiceMass_eq_aggregateDemand Finset.univ)
      (inst.selected_choiceMass_eq_aggregateDemand small) inst.selected_clearing
      inst.literal.totalCapacity_eq hsmall_card halpha_nonneg
      inst.capacity_regular hden_pos
  have hsmall_at_anchor :
      theorem2_twoScaleSmallFirmSourceBound totalSupply alpha delta endpoint sigma
        (cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small anchor
          inst.selectedCutoffVector) :=
    theorem2_twoScaleSmallFirmSourceBound_at_or_below_vStar
      noiseLaw small inst.selectedCutoffVector hanchor_star hsmall_at_star
  have hsmall_at_target :
      theorem2_twoScaleSmallFirmSourceBound totalSupply (K * alpha) delta
        endpoint sigma
        (cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small target
          inst.selectedCutoffVector) := by
    unfold theorem2_twoScaleSmallFirmSourceBound at hsmall_at_anchor ⊢
    calc
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small target
          inst.selectedCutoffVector ≤
          K * cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) small anchor
            inst.selectedCutoffVector := hsmall_scale
      _ ≤ K * (alpha * Real.sqrt delta /
            theorem2_twoScaleDenominator totalSupply delta endpoint sigma) :=
        mul_le_mul_of_nonneg_left hsmall_at_anchor hK_nonneg
      _ = (K * alpha) * Real.sqrt delta /
            theorem2_twoScaleDenominator totalSupply delta endpoint sigma := by
        ring
  exact theorem2_twoScaleCutoffRegularWindow_of_checked_block_bounds
    noiseLaw small large hcover inst.selectedCutoffVector hv_low
    hlarge_high_lower_scaled hlarge_endpoint_gap hlarge_residual hsmall_at_target

/-- The literal basic-model Theorem 2 conclusion for every fixed real target.
The construction repairs the appendix's bounded-support quantifier gap while
preserving uniformity over all admissible selected clearing instances. -/
theorem theorem2_eventually_allRealTargetAbsBound_uniform_of_holder_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {Admissible : ℕ → Type v} (CutoffSeq : ℕ → Type w)
    {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : ∀ C : ℕ, Admissible C →
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (hregular : PG24HolderIntervalRegular eta)
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) :
    ∀ target tolerance : ℝ, 0 < tolerance →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        |cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) target
            (inst C a).selectedCutoffVector - totalSupply| < tolerance := by
  letI : NoAtoms eta := hregular.noAtoms
  rcases exists_supportInterior_anchor_of_holder eta hregular with
    ⟨anchor, hanchor_lower, hanchor_upper⟩
  intro target tolerance htolerance_pos
  by_cases htarget_le_anchor : target ≤ anchor
  · rcases theorem2_exists_split_gap_budget_for_fixed_tolerance_at_interior_target
        (totalSupply := totalSupply) (alpha := alpha) (tol := tolerance)
        (eta := eta) (v := anchor) htotalSupply_lt_one halpha_nonneg
        htolerance_pos hanchor_lower hanchor_upper with
      ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
        _hbudget_den_pos, _hlower_budget, _hupper_budget,
        hanchor_lower_budget, hanchor_upper_budget, htransfer⟩
    rcases theorem2_exists_exactQuantileWindow_of_noAtoms
        eta hdelta_pos hquantile with
      ⟨vLow, vHigh, vStar, hwindow⟩
    have hanchor_member :
        theorem2_localWindowMembership vLow vHigh vStar anchor :=
      theorem2_localWindowMembership_of_exactQuantileWindow_of_interiorBudgets
        eta hwindow hanchor_lower_budget hanchor_upper_budget
    let analysisLow := min target vLow
    have hanalysisLow_lt_high : analysisLow < vHigh :=
      lt_of_le_of_lt (min_le_right target vLow) hwindow.lower_lt_upper
    rcases
        theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_uniform_of_longTailed
          CutoffSeq noiseLaw eta hlong hdelta_pos hgap_pos
          htotalSupply_lt_one hanalysisLow_lt_high inst with
      ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one,
        hgap, hfailure⟩
    rcases htransfer endpoint sigma hgap with
      ⟨hden_pos, hlower_error, hupper_error⟩
    rcases hwindow.valueRegions with
      ⟨hlarge_meas, hlarge_mass, hlarge_ge, hlarge_le_high,
        hsmall_meas, hsmall_mass, hsmall_ge, hsmall_le_high⟩
    filter_upwards [hfailure] with C hfailureC a
    have hregular_window :=
      theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
        (inst C a) (hfailureC a).1 hlarge_meas hlarge_mass
        (fun value hvalue =>
          le_trans (min_le_right target vLow) (hlarge_ge value hvalue))
        hlarge_le_high hsmall_meas hsmall_mass hsmall_ge hsmall_le_high
        hdelta_pos htotalSupply_pos.le hsupply_split hden_pos.le
        hendpoint_pos.le hsigma_pos.le
        (min_le_left target vLow)
        (htarget_le_anchor.trans hanchor_member.2.1)
        (htarget_le_anchor.trans hanchor_member.2.2)
        (fun c hc => ((hfailureC a).2 c hc).1)
        (fun c hc => ((hfailureC a).2 c hc).2.1)
        (fun c hc => ((hfailureC a).2 c hc).2.2)
        halpha_nonneg hden_pos
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hregular_window.1, hregular_window.2]
  · have hanchor_le_target : anchor ≤ target :=
      le_of_lt (lt_of_not_ge htarget_le_anchor)
    rcases exists_cutoffAffordanceProbability_value_multiplier_of_longTailed
        noiseLaw hlong hanchor_le_target with
      ⟨K, hK, hscale⟩
    have hK_nonneg : 0 ≤ K := le_trans (by norm_num) hK
    have hscaled_alpha_nonneg : 0 ≤ K * alpha :=
      mul_nonneg hK_nonneg halpha_nonneg
    rcases theorem2_exists_split_gap_budget_for_fixed_tolerance_at_interior_target
        (totalSupply := totalSupply) (alpha := K * alpha) (tol := tolerance)
        (eta := eta) (v := anchor) htotalSupply_lt_one hscaled_alpha_nonneg
        htolerance_pos hanchor_lower hanchor_upper with
      ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
        _hbudget_den_pos, _hlower_budget, _hupper_budget,
        hanchor_lower_budget, hanchor_upper_budget, htransfer⟩
    rcases theorem2_exists_exactQuantileWindow_of_noAtoms
        eta hdelta_pos hquantile with
      ⟨vLow, vHigh, vStar, hwindow⟩
    have hanchor_member :
        theorem2_localWindowMembership vLow vHigh vStar anchor :=
      theorem2_localWindowMembership_of_exactQuantileWindow_of_interiorBudgets
        eta hwindow hanchor_lower_budget hanchor_upper_budget
    let analysisHigh := max target vHigh
    have hlow_lt_analysisHigh : vLow < analysisHigh :=
      lt_of_lt_of_le hwindow.lower_lt_upper (le_max_right target vHigh)
    rcases
        theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_uniform_of_longTailed
          CutoffSeq noiseLaw eta hlong hdelta_pos hgap_pos
          htotalSupply_lt_one hlow_lt_analysisHigh inst with
      ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one,
        hgap, hfailure⟩
    rcases htransfer endpoint sigma hgap with
      ⟨hden_pos, hlower_error, hupper_error⟩
    rcases hwindow.valueRegions with
      ⟨hlarge_meas, hlarge_mass, hlarge_ge, hlarge_le_high,
        hsmall_meas, hsmall_mass, hsmall_ge, hsmall_le_high⟩
    filter_upwards [hfailure] with C hfailureC a
    let floor : ℝ :=
      analysisHigh + theorem4HighTailQuantile noiseLaw sigma C
    let small : Finset (Fin (C + 1)) :=
      lowCutoffIndexSet (inst C a).selectedCutoffVector floor
    let large : Finset (Fin (C + 1)) :=
      nonLowCutoffIndexSet (inst C a).selectedCutoffVector floor
    have hsmall_subset :
        small ⊆ (Finset.univ : Finset (Fin (C + 1))) := by
      intro c _hc
      simp
    have hdisjoint : Disjoint small large := by
      simpa [small, large, nonLowCutoffIndexSet] using
        (Finset.disjoint_sdiff :
          Disjoint small ((Finset.univ : Finset (Fin (C + 1))) \ small))
    have hcover :
        small ∪ large = (Finset.univ : Finset (Fin (C + 1))) := by
      simpa [small, large, nonLowCutoffIndexSet] using
        (Finset.union_sdiff_of_subset hsmall_subset)
    have hlarge_eq :
        large = theorem2LiteralLargeCutoffBlock
          (inst C a).literal analysisHigh sigma := by
      dsimp [large, floor, theorem2LiteralLargeCutoffBlock]
      rw [(inst C a).selectedCutoffVector_eq_localCutoff]
    have hlarge :
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          large delta := by
      rw [hlarge_eq]
      exact (hfailureC a).1
    have hsmall_card :
        (small.card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ) := by
      exact lowCutoffIndexSet_card_le_of_coalitionLargeSubset_nonLow hlarge
    have hfailure_selected :
        ∀ c ∈ large,
          Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((inst C a).selectedCutoffVector c - analysisHigh)) /
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((inst C a).selectedCutoffVector c - vLow)) := by
      intro c hc
      rw [(inst C a).selectedCutoffVector_eq_localCutoff]
      exact ((hfailureC a).2 c (by simpa [hlarge_eq] using hc)).1
    have hlow_failure_pos_selected :
        ∀ c ∈ large,
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            ((inst C a).selectedCutoffVector c - vLow) := by
      intro c hc
      rw [(inst C a).selectedCutoffVector_eq_localCutoff]
      exact ((hfailureC a).2 c (by simpa [hlarge_eq] using hc)).2.1
    have hlow_failure_le_one_selected :
        ∀ c ∈ large,
          1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            ((inst C a).selectedCutoffVector c - vLow) ≤ 1 := by
      intro c hc
      rw [(inst C a).selectedCutoffVector_eq_localCutoff]
      exact ((hfailureC a).2 c (by simpa [hlarge_eq] using hc)).2.2
    have hregular_window :=
      theorem2_twoScaleRegularWindow_of_literalBasic_highTarget
        (inst C a) small large hdisjoint hcover hlarge_meas hlarge_mass
        hlarge_ge
        (fun value hvalue =>
          (hlarge_le_high value hvalue).trans (le_max_right target vHigh))
        hsmall_meas hsmall_mass hsmall_ge
        (fun value hvalue =>
          (hsmall_le_high value hvalue).trans (le_max_right target vHigh))
        hdelta_pos htotalSupply_pos.le hsupply_split hden_pos.le
        hendpoint_pos.le hsigma_pos.le
        (hanchor_member.1.trans hanchor_le_target)
        (le_max_left target vHigh) hanchor_member.2.2 hfailure_selected
        hlow_failure_pos_selected hlow_failure_le_one_selected hsmall_card hK
        (hscale (C + 1) small (inst C a).selectedCutoffVector)
        halpha_nonneg hden_pos
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hregular_window.1, hregular_window.2]

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
