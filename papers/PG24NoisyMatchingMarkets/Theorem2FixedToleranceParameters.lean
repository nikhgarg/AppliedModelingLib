import PG24NoisyMatchingMarkets.Theorem2TwoScaleLiteralSourceClosure

/-!
# PG24 Theorem 2 fixed-tolerance two-scale parameters

This module keeps the two parameter choices in their valid order.  A small
split is selected for the requested final tolerance.  Only after a scale has
been selected for that split is the endpoint accuracy selected to fit the
remaining product-gap budget.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

private theorem theorem2_fixedTolerance_split_pos (n : ℕ) :
    0 < AppliedModelingLib.Math.invSqrtSuccError n := by
  unfold AppliedModelingLib.Math.invSqrtSuccError
  positivity

private theorem theorem2_fixedTolerance_sqrt_split_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
      atTop (nhds 0) := by
  have hsplit :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  simpa [Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsplit

private theorem theorem2_fixedTolerance_lowerBudget_tendsto_zero
    (alpha : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (1 + alpha) * AppliedModelingLib.Math.invSqrtSuccError n +
          AppliedModelingLib.Math.invSqrtSuccError n)
      atTop (nhds 0) := by
  have hsplit :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hlinear :
      Tendsto
        (fun n : ℕ => (1 + alpha) * AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hsplit : Tendsto
        (fun n : ℕ => (1 + alpha) * AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds ((1 + alpha) * 0)))
  simpa using hlinear.add hsplit

private theorem theorem2_fixedTolerance_denominatorBudget_tendsto
    (totalSupply : ℝ) :
    Tendsto
      (fun n : ℕ =>
        1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
          AppliedModelingLib.Math.invSqrtSuccError n)
      atTop (nhds (1 - totalSupply)) := by
  have hsplit :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hbase :
      Tendsto
        (fun n : ℕ => 1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds (1 - totalSupply)) := by
    simpa using
      (tendsto_const_nhds.sub hsplit : Tendsto
        (fun n : ℕ => (1 - totalSupply) - AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds ((1 - totalSupply) - 0)))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    hbase.sub hsplit

private theorem theorem2_fixedTolerance_upperBudget_tendsto_zero
    {totalSupply alpha : ℝ} (htotalSupply_lt_one : totalSupply < 1) :
    Tendsto
      (fun n : ℕ =>
        AppliedModelingLib.Math.invSqrtSuccError n +
          AppliedModelingLib.Math.invSqrtSuccError n +
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n) /
            (1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
              AppliedModelingLib.Math.invSqrtSuccError n))
      atTop (nhds 0) := by
  have hsplit :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hsqrt := theorem2_fixedTolerance_sqrt_split_tendsto_zero
  have hnum :
      Tendsto
        (fun n : ℕ => alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hsqrt : Tendsto
        (fun n : ℕ => alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds (alpha * 0)))
  have hden := theorem2_fixedTolerance_denominatorBudget_tendsto totalSupply
  have hden_ne : 1 - totalSupply ≠ 0 := by
    linarith
  have hquot :
      Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n) /
            (1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
              AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds 0) := by
    simpa using
      (hnum.div hden hden_ne : Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n) /
            (1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
              AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds (0 / (1 - totalSupply))))
  simpa [add_assoc] using (hsplit.add hsplit).add hquot

/--
Choose a split and a strictly positive independent-product-gap budget for one
requested final tolerance.  Any later endpoint/scale pair whose actual gap is
below that budget has a positive small-firm denominator and both displayed
two-scale errors below the requested tolerance.

The universal final clause is deliberately independent of how the later scale
is obtained.  It is what permits the semantic long-tail cutoff construction to
select the scale after the split, instead of reusing the invalid one-scale
schedule from the appendix.
-/
theorem theorem2_exists_split_gap_budget_for_fixed_tolerance
    {totalSupply alpha tol : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol) :
    ∃ delta gap : ℝ,
      0 < delta ∧
      Real.sqrt delta + delta / 2 < 1 ∧
      totalSupply + delta < 1 ∧
      0 < gap ∧
      0 < 1 - totalSupply - delta - gap ∧
      (1 + alpha) * delta + gap < tol ∧
      delta + gap + alpha * Real.sqrt delta /
          (1 - totalSupply - delta - gap) < tol ∧
      ∀ endpoint sigma : ℝ,
        1 - Real.exp (-(2 * endpoint * sigma)) < gap →
          0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
          theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
          theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol := by
  let split : ℕ → ℝ := AppliedModelingLib.Math.invSqrtSuccError
  have hsplit_zero : Tendsto split atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hden_pos : ∀ᶠ n : ℕ in atTop,
      0 < 1 - totalSupply - split n - split n := by
    have hslack_pos : 0 < 1 - totalSupply := by linarith
    exact (theorem2_fixedTolerance_denominatorBudget_tendsto totalSupply)
      (isOpen_Ioi.mem_nhds hslack_pos)
  have hlower_small : ∀ᶠ n : ℕ in atTop,
      (1 + alpha) * split n + split n < tol :=
    (theorem2_fixedTolerance_lowerBudget_tendsto_zero alpha)
      (isOpen_Iio.mem_nhds htol_pos)
  have hupper_small : ∀ᶠ n : ℕ in atTop,
      split n + split n + alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n - split n) < tol := by
    exact (theorem2_fixedTolerance_upperBudget_tendsto_zero
      (totalSupply := totalSupply) (alpha := alpha) htotalSupply_lt_one)
      (isOpen_Iio.mem_nhds htol_pos)
  have hsqrt_small : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (split n) + split n < 1 := by
    have hsqrt_zero : Tendsto (fun n : ℕ => Real.sqrt (split n))
        atTop (nhds 0) := by
      simpa [split] using theorem2_fixedTolerance_sqrt_split_tendsto_zero
    have hsum : Tendsto (fun n : ℕ => Real.sqrt (split n) + split n)
        atTop (nhds 0) := by
      simpa using hsqrt_zero.add hsplit_zero
    exact hsum (isOpen_Iio.mem_nhds (by norm_num))
  rcases (hden_pos.and (hlower_small.and (hupper_small.and hsqrt_small))).exists with
    ⟨n, hden_n, hlower_n, hupper_n, hsqrt_n⟩
  have hdelta_pos : 0 < split n := by
    simpa [split] using theorem2_fixedTolerance_split_pos n
  have hquantile : Real.sqrt (split n) + split n / 2 < 1 := by
    have hhalf_le : split n / 2 ≤ split n := by linarith
    linarith
  have hsupply_split : totalSupply + split n < 1 := by
    linarith
  refine ⟨split n, split n, hdelta_pos, hquantile, hsupply_split,
    hdelta_pos, hden_n, hlower_n, hupper_n, ?_⟩
  intro endpoint sigma hgap
  have hactual_den_pos :
      0 < 1 - totalSupply - split n -
        (1 - Real.exp (-(2 * endpoint * sigma))) := by
    linarith
  have hbudget_den_le_actual :
      1 - totalSupply - split n - split n ≤
        1 - totalSupply - split n -
          (1 - Real.exp (-(2 * endpoint * sigma))) := by
    linarith
  have hnumerator_nonneg : 0 ≤ alpha * Real.sqrt (split n) :=
    mul_nonneg halpha_nonneg (Real.sqrt_nonneg _)
  have hquot_le :
      alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n -
            (1 - Real.exp (-(2 * endpoint * sigma)))) ≤
        alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n - split n) := by
    exact div_le_div_of_nonneg_left hnumerator_nonneg hden_n
      hbudget_den_le_actual
  constructor
  · simpa [theorem2_twoScaleDenominator, theorem2_twoScaleProductGap] using
      hactual_den_pos
  constructor
  · unfold theorem2_twoScaleLowerError
    linarith
  · unfold theorem2_twoScaleUpperError
    linarith

/--
The fixed-tolerance split/gap selection can also be made small enough for one
support-interior target.  The two final inequalities are exactly the lower and
upper mass budgets used to place that target inside a subsequently chosen
fixed quantile window.
-/
theorem theorem2_exists_split_gap_budget_for_fixed_tolerance_at_interior_target
    {totalSupply alpha tol : ℝ} {eta : Measure ℝ} {v : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol)
    (hv_lower : 0 < eta.real (Set.Iio v))
    (hv_upper : 0 < eta.real (Set.Ioi v)) :
    ∃ delta gap : ℝ,
      0 < delta ∧
      Real.sqrt delta + delta / 2 < 1 ∧
      totalSupply + delta < 1 ∧
      0 < gap ∧
      0 < 1 - totalSupply - delta - gap ∧
      (1 + alpha) * delta + gap < tol ∧
      delta + gap + alpha * Real.sqrt delta /
          (1 - totalSupply - delta - gap) < tol ∧
      delta / 2 < eta.real (Set.Iio v) ∧
      Real.sqrt delta + delta / 2 < eta.real (Set.Ioi v) ∧
      ∀ endpoint sigma : ℝ,
        1 - Real.exp (-(2 * endpoint * sigma)) < gap →
          0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
          theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
          theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol := by
  let split : ℕ → ℝ := AppliedModelingLib.Math.invSqrtSuccError
  have hsplit_zero : Tendsto split atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hden_pos : ∀ᶠ n : ℕ in atTop,
      0 < 1 - totalSupply - split n - split n := by
    have hslack_pos : 0 < 1 - totalSupply := by linarith
    exact (theorem2_fixedTolerance_denominatorBudget_tendsto totalSupply)
      (isOpen_Ioi.mem_nhds hslack_pos)
  have hlower_small : ∀ᶠ n : ℕ in atTop,
      (1 + alpha) * split n + split n < tol :=
    (theorem2_fixedTolerance_lowerBudget_tendsto_zero alpha)
      (isOpen_Iio.mem_nhds htol_pos)
  have hupper_small : ∀ᶠ n : ℕ in atTop,
      split n + split n + alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n - split n) < tol := by
    exact (theorem2_fixedTolerance_upperBudget_tendsto_zero
      (totalSupply := totalSupply) (alpha := alpha) htotalSupply_lt_one)
      (isOpen_Iio.mem_nhds htol_pos)
  have hsqrt_zero : Tendsto (fun n : ℕ => Real.sqrt (split n))
      atTop (nhds 0) := by
    simpa [split] using theorem2_fixedTolerance_sqrt_split_tendsto_zero
  have hhalf_zero : Tendsto (fun n : ℕ => split n / 2)
      atTop (nhds 0) := by
    simpa using
      (hsplit_zero.div tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0))
  have hsqrt_half_zero : Tendsto
      (fun n : ℕ => Real.sqrt (split n) + split n / 2)
      atTop (nhds 0) := by
    simpa using hsqrt_zero.add hhalf_zero
  have hquantile_small : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (split n) + split n / 2 < 1 :=
    hsqrt_half_zero (isOpen_Iio.mem_nhds (by norm_num))
  have htarget_lower : ∀ᶠ n : ℕ in atTop,
      split n / 2 < eta.real (Set.Iio v) :=
    hhalf_zero (isOpen_Iio.mem_nhds hv_lower)
  have htarget_upper : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (split n) + split n / 2 < eta.real (Set.Ioi v) :=
    hsqrt_half_zero (isOpen_Iio.mem_nhds hv_upper)
  rcases (hden_pos.and
      (hlower_small.and (hupper_small.and (hquantile_small.and
        (htarget_lower.and htarget_upper))))).exists with
    ⟨n, hden_n, hlower_n, hupper_n, hquantile_n, htarget_lower_n,
      htarget_upper_n⟩
  have hdelta_pos : 0 < split n := by
    simpa [split] using theorem2_fixedTolerance_split_pos n
  have hsupply_split : totalSupply + split n < 1 := by
    linarith
  refine ⟨split n, split n, hdelta_pos, hquantile_n, hsupply_split,
    hdelta_pos, hden_n, hlower_n, hupper_n, htarget_lower_n,
    htarget_upper_n, ?_⟩
  intro endpoint sigma hgap
  have hactual_den_pos :
      0 < 1 - totalSupply - split n -
        (1 - Real.exp (-(2 * endpoint * sigma))) := by
    linarith
  have hbudget_den_le_actual :
      1 - totalSupply - split n - split n ≤
        1 - totalSupply - split n -
          (1 - Real.exp (-(2 * endpoint * sigma))) := by
    linarith
  have hnumerator_nonneg : 0 ≤ alpha * Real.sqrt (split n) :=
    mul_nonneg halpha_nonneg (Real.sqrt_nonneg _)
  have hquot_le :
      alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n -
            (1 - Real.exp (-(2 * endpoint * sigma)))) ≤
        alpha * Real.sqrt (split n) /
          (1 - totalSupply - split n - split n) := by
    exact div_le_div_of_nonneg_left hnumerator_nonneg hden_n
      hbudget_den_le_actual
  constructor
  · simpa [theorem2_twoScaleDenominator, theorem2_twoScaleProductGap] using
      hactual_den_pos
  constructor
  · unfold theorem2_twoScaleLowerError
    linarith
  · unfold theorem2_twoScaleUpperError
    linarith

/--
The scalar capacity-selection inequality from the appendix is compatible with
the repaired two-stage choice: select the split for final error first, then a
capacity scale, and finally an endpoint error after that scale.

This is a numerical parameter theorem only.  The separate literal-source
closure supplies the semantic cutoff geometry needed by the market proof.
-/
theorem theorem2_exists_fixed_twoScale_capacity_parameters_for_tolerance
    {totalSupply alpha tol : ℝ}
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol) :
    ∃ delta sigma endpoint : ℝ,
      0 < delta ∧
      Real.sqrt delta + delta / 2 < 1 ∧
      totalSupply + delta < 1 ∧
      0 < sigma ∧
      totalSupply <
        (1 - delta) *
          (1 - Real.exp (-(delta * (1 - delta) * sigma))) ∧
      0 < endpoint ∧ endpoint ≤ 1 ∧
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
      theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
      theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol := by
  rcases theorem2_exists_split_gap_budget_for_fixed_tolerance
      htotalSupply_lt_one halpha_nonneg htol_pos with
    ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
      hbudget_den_pos, hlower_budget, hupper_budget, htransfer⟩
  have hdelta_lt_one : delta < 1 := by
    linarith
  have hcapacity_input : totalSupply < 1 - delta := by
    linarith
  rcases theorem2_exists_capacity_scale_after_split
      hdelta_pos hdelta_lt_one hcapacity_input with
    ⟨sigma, hsigma_pos, hcapacity⟩
  rcases theorem2_exists_endpoint_error_after_scale hgap_pos hsigma_pos with
    ⟨endpoint, hendpoint_pos, hendpoint_le_one, hgap⟩
  rcases htransfer endpoint sigma hgap with ⟨hden_pos, hlower, hupper⟩
  exact ⟨delta, sigma, endpoint, hdelta_pos, hquantile, hsupply_split,
    hsigma_pos, hcapacity, hendpoint_pos, hendpoint_le_one, hden_pos,
    hlower, hupper⟩

/--
For fixed source endpoints, the literal long-tail construction composes with
the split/gap budget.  It selects the semantic cutoff scale after the split,
then the endpoint accuracy after that scale, and returns a final window whose
two scalar errors meet the external tolerance.

The endpoints remain fixed in this theorem.  In particular, this result does
not claim a long-tail failure-ratio bound for a value-dependent or
varying-quantile schedule.
-/
theorem theorem2_literalSource_exists_fixedTolerance_parameters_of_longTailed
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply alpha tol vLow vHigh : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha) (htol_pos : 0 < tol)
    (hv : vLow < vHigh)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) :
    ∃ delta sigma endpoint : ℝ,
      0 < delta ∧
      Real.sqrt delta + delta / 2 < 1 ∧
      totalSupply + delta < 1 ∧
      0 < sigma ∧ 0 < endpoint ∧ endpoint ≤ 1 ∧
      0 < theorem2_twoScaleDenominator totalSupply delta endpoint sigma ∧
      theorem2_twoScaleLowerError alpha delta endpoint sigma < tol ∧
      theorem2_twoScaleUpperError totalSupply alpha delta endpoint sigma < tol ∧
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (Finset.univ : Finset (Fin (C + 1)))
          (theorem2LiteralLargeCutoffBlock (data C) vHigh sigma) delta ∧
        ∀ c ∈ theorem2LiteralLargeCutoffBlock (data C) vHigh sigma,
          Real.exp (-(2 * endpoint * sigma / ((C + 1 : ℕ) : ℝ))) ≤
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c -
                  vHigh)) /
                (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c -
                    vLow)) ∧
            0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c -
                vLow) ∧
            1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c -
                vLow) ≤ 1 := by
  rcases theorem2_exists_split_gap_budget_for_fixed_tolerance
      htotalSupply_lt_one halpha_nonneg htol_pos with
    ⟨delta, gap, hdelta_pos, hquantile, hsupply_split, hgap_pos,
      hbudget_den_pos, hlower_budget, hupper_budget, htransfer⟩
  rcases theorem2_literalSource_exists_sigma_endpoint_nonLowFailureRatio_of_longTailed
      CutoffSeq noiseLaw eta hlong hdelta_pos hgap_pos htotalSupply_lt_one hv data with
    ⟨sigma, endpoint, hsigma_pos, hendpoint_pos, hendpoint_le_one, hgap,
      hfailure⟩
  rcases htransfer endpoint sigma hgap with ⟨hden_pos, hlower, hupper⟩
  exact ⟨delta, sigma, endpoint, hdelta_pos, hquantile, hsupply_split,
    hsigma_pos, hendpoint_pos, hendpoint_le_one, hden_pos, hlower, hupper,
    hfailure⟩

end

end PG24NoisyMatchingMarkets
