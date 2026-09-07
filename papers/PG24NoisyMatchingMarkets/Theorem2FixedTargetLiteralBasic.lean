import PG24NoisyMatchingMarkets.Theorem2FixedToleranceParameters
import PG24NoisyMatchingMarkets.Theorem2LiteralBasicAmplificationRoute
import PG24NoisyMatchingMarkets.Theorem2QuantileSchedule

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
A fixed exact quantile window contains a support-interior target when its two
source mass budgets are below the target's lower and upper open-tail masses.
-/
theorem theorem2_localWindowMembership_of_exactQuantileWindow_of_interiorBudgets
    (eta : Measure ℝ) [IsProbabilityMeasure eta] [NoAtoms eta]
    {delta vLow vHigh vStar target : ℝ}
    (hwindow : Theorem2ExactQuantileWindow eta delta vLow vHigh vStar)
    (htarget_lower : delta / 2 < eta.real (Set.Iio target))
    (htarget_upper : Real.sqrt delta + delta / 2 < eta.real (Set.Ioi target)) :
    theorem2_localWindowMembership vLow vHigh vStar target := by
  have hvlow_lt : vLow < target := by
    by_contra hnot
    have horder : target ≤ vLow := le_of_not_gt hnot
    have hmono : eta.real (Set.Iio target) ≤ eta.real (Set.Iio vLow) :=
      MeasureTheory.measureReal_mono
        (by
          intro x hx
          exact lt_of_lt_of_le hx horder)
        (measure_ne_top eta _)
    rw [hwindow.lower_tail] at hmono
    linarith
  have hvstar_tail : eta.real (Set.Ioi vStar) ≤ Real.sqrt delta + delta / 2 := by
    apply theorem2_upperTailMass_le_of_open_quantile_window_noAtoms eta
      hwindow.star_lt_upper.le
    · exact le_of_eq hwindow.middle_mass
    · simpa [AppliedModelingLib.Probability.upperTailMass] using
        le_of_eq hwindow.upper_tail
  have htarget_lt_star : target < vStar := by
    by_contra hnot
    have horder : vStar ≤ target := le_of_not_gt hnot
    have hmono : eta.real (Set.Ioi target) ≤ eta.real (Set.Ioi vStar) :=
      MeasureTheory.measureReal_mono
        (by
          intro x hx
          exact lt_of_le_of_lt horder hx)
        (measure_ne_top eta _)
    linarith
  exact ⟨le_of_lt hvlow_lt,
    le_of_lt (lt_trans htarget_lt_star hwindow.star_lt_upper),
    le_of_lt htarget_lt_star⟩

universe u w

namespace PG24LiteralBasicTwoScaleInstance

/--
For one fixed support-interior target and final tolerance, choose a split,
fixed source quantiles, a semantic cutoff scale, and an endpoint accuracy in
that order.  The result is an eventual literal-basic two-scale regular window.

This is intentionally pointwise in `target`: long-tailedness is applied only
after `vLow` and `vHigh` have been fixed, so no uniform claim over a
varying-quantile schedule is used.
-/
theorem theorem2_exists_eventually_fixedTargetRegularWindow_of_holder_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    (CutoffSeq : ℕ → Type w)
    {noiseLaw eta : Measure ℝ} {totalSupply alpha target tol : ℝ}
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (hregular : PG24HolderIntervalRegular eta)
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (htarget_lower : 0 < eta.real (Set.Iio target))
    (htarget_upper : 0 < eta.real (Set.Ioi target))
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol) :
    ∃ delta sigma endpoint vLow vHigh vStar : ℝ,
      Theorem2ExactQuantileWindow eta delta vLow vHigh vStar ∧
      theorem2_localWindowMembership vLow vHigh vStar target ∧
      0 < delta ∧
      totalSupply + delta < 1 ∧
      0 < sigma ∧ 0 < endpoint ∧ endpoint ≤ 1 ∧
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
      theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
      theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol ∧
      ∀ᶠ C : ℕ in atTop,
        theorem2TwoScaleRegularWindow totalSupply alpha delta endpoint sigma
          (cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) target
            (inst C).selectedCutoffVector) := by
  letI : NoAtoms eta := hregular.noAtoms
  rcases theorem2_exists_split_gap_budget_for_fixed_tolerance_at_interior_target
      htotalSupply_lt_one halpha_nonneg htol_pos htarget_lower htarget_upper with
    ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
      hbudget_den_pos, hlower_budget, hupper_budget, htarget_lower_budget,
      htarget_upper_budget, htransfer⟩
  rcases theorem2_exists_exactQuantileWindow_of_noAtoms
      eta hdelta_pos hquantile with
    ⟨vLow, vHigh, vStar, hwindow⟩
  have hmember : theorem2_localWindowMembership vLow vHigh vStar target :=
    theorem2_localWindowMembership_of_exactQuantileWindow_of_interiorBudgets
      eta hwindow htarget_lower_budget htarget_upper_budget
  rcases theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_of_longTailed
      CutoffSeq noiseLaw eta hlong hdelta_pos hgap_pos htotalSupply_lt_one
      hwindow.lower_lt_upper (fun C => (inst C).literal) with
    ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one, hgap,
      hfailure⟩
  rcases htransfer endpoint sigma hgap with ⟨hden_pos, hlower, hupper⟩
  refine ⟨delta, sigma, endpoint, vLow, vHigh, vStar, hwindow, hmember,
    hdelta_pos, hsupply_split, hsigma_pos, hendpoint_pos, hendpoint_le_one,
    hden_pos, hlower, hupper, ?_⟩
  rcases hwindow.valueRegions with
    ⟨hlarge_meas, hlarge_mass, hlarge_ge, hlarge_le_high, hsmall_meas,
      hsmall_mass, hsmall_ge, hsmall_le_high⟩
  rcases hmember with ⟨htarget_low, htarget_high, htarget_star⟩
  filter_upwards [hfailure] with C hfailureC
  refine theorem2_twoScaleRegularWindow_of_literalBasic_literalNonLowFailureRatio
    (inst C) hfailureC.1 hlarge_meas hlarge_mass hlarge_ge hlarge_le_high
    hsmall_meas hsmall_mass hsmall_ge hsmall_le_high
    hdelta_pos htotalSupply_pos.le hsupply_split hden_pos.le
    hendpoint_pos.le hsigma_pos.le htarget_low htarget_high htarget_star ?_ ?_ ?_
    halpha_nonneg hden_pos
  · intro c hc
    exact (hfailureC.2 c hc).1
  · intro c hc
    exact (hfailureC.2 c hc).2.1
  · intro c hc
    exact (hfailureC.2 c hc).2.2

end PG24LiteralBasicTwoScaleInstance

end

end PG24NoisyMatchingMarkets
