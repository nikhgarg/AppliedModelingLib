import Mathlib.Tactic

/-!
# LG24 Current-Draft Algebra Checks

This paper-local module checks the scalar algebra used in the current draft of
*Redesigning Service Level Agreements: Equity and Efficiency in City Government
Operations*.  It isolates the corrected Proposition 2.1 recovery map, records
concrete counterexamples to two inconsistent printed formulas, and derives the
one-category/two-Borough endpoint comparisons from named endpoint losses.

The variables `u` and `v` below stand for
`sqrt (lambda_1 * r_1)` and `sqrt (lambda_2 * r_2)`.  The variable `slack`
stands for the positive excess capacity `C - lambda_1 - lambda_2`.

## Main declarations

- `proposition2_1_recoveredGPSWeight_slack_eq`: the corrected recovery
  `phi = (x + lambda) / C` recovers slack `x`.
- `proposition2_1_printed_minus_recovery_counterexample`: a feasible-looking
  numerical instance where the printed minus-sign recovery fails.
- `currentDraft_extremeEquity_reciprocal_counterexample`: the printed
  `r / (lambda * x)` term differs from the cost-consistent `lambda * r / x`.
- `twoBorough_priceOfEquity_eq` and
  `twoBorough_priceOfEfficiency_eq_of_v_le_u`: the two endpoint prices.
- `twoBorough_poolingGain_eq` and
  `twoBorough_priceMinusPooling_eq`: the pooling comparison identities.
-/

namespace LG24ServiceLevelAgreements

noncomputable section

/-! ## Proposition 2.1 recovery map -/

/-- Slack induced by capacity `C`, GPS weight `phi`, and arrival rate `lambda`. -/
def gpsSlack (capacity weight arrivalRate : ℝ) : ℝ :=
  capacity * weight - arrivalRate

/--
Correct recovery map for Proposition 2.1:
`phi = (x + lambda) / C`.
-/
def recoveredGPSWeight (x arrivalRate capacity : ℝ) : ℝ :=
  (x + arrivalRate) / capacity

/-- The minus-sign recovery currently printed in the manuscript draft. -/
def printedMinusGPSWeight (x arrivalRate capacity : ℝ) : ℝ :=
  (x - arrivalRate) / capacity

/-- The corrected Proposition 2.1 recovery map recovers exactly the chosen slack. -/
theorem proposition2_1_recoveredGPSWeight_slack_eq
    {x arrivalRate capacity : ℝ} (hcapacity : capacity ≠ 0) :
    gpsSlack capacity (recoveredGPSWeight x arrivalRate capacity) arrivalRate = x := by
  unfold gpsSlack recoveredGPSWeight
  field_simp [hcapacity]
  ring

/-- Conversely, every weight inducing slack `x` equals the corrected recovery map. -/
theorem gpsWeight_eq_recoveredGPSWeight_of_slack_eq
    {x arrivalRate capacity weight : ℝ}
    (hcapacity : capacity ≠ 0)
    (hslack : gpsSlack capacity weight arrivalRate = x) :
    weight = recoveredGPSWeight x arrivalRate capacity := by
  unfold gpsSlack at hslack
  unfold recoveredGPSWeight
  apply (eq_div_iff hcapacity).2
  nlinarith [hslack]

/--
At `x = 3`, `lambda = 2`, and `C = 10`, the corrected weight is `1/2` and
does recover slack `3`.
-/
theorem proposition2_1_corrected_recovery_example :
    recoveredGPSWeight 3 2 10 = (1 / 2 : ℝ) ∧
      gpsSlack 10 (recoveredGPSWeight 3 2 10) 2 = 3 := by
  norm_num [recoveredGPSWeight, gpsSlack]

/--
Concrete counterexample to the printed minus sign.  At `x = 3`, `lambda = 2`,
and `C = 10`, the printed map returns the positive weight `1/10`, but its
induced slack is `-1`, not `3`.
-/
theorem proposition2_1_printed_minus_recovery_counterexample :
    printedMinusGPSWeight 3 2 10 = (1 / 10 : ℝ) ∧
      gpsSlack 10 (printedMinusGPSWeight 3 2 10) 2 = -1 ∧
      gpsSlack 10 (printedMinusGPSWeight 3 2 10) 2 ≠ 3 := by
  norm_num [printedMinusGPSWeight, gpsSlack]

/-! ## Current-draft extreme-equity reciprocal check -/

/-- The reciprocal term `r / (lambda * x)` printed in the current draft. -/
def printedExtremeEquityReciprocalTerm
    (risk arrivalRate x : ℝ) : ℝ :=
  risk / (arrivalRate * x)

/-- The term `lambda * r / x` induced by the draft's stated Borough cost. -/
def costConsistentExtremeEquityReciprocalTerm
    (risk arrivalRate x : ℝ) : ℝ :=
  arrivalRate * risk / x

/--
Concrete check that `r / (lambda * x)` cannot in general be substituted for
`lambda * r / x`: at `(r, lambda, x) = (1, 2, 1)` they are `1/2` and `2`.
-/
theorem currentDraft_extremeEquity_reciprocal_counterexample :
    printedExtremeEquityReciprocalTerm 1 2 1 = (1 / 2 : ℝ) ∧
      costConsistentExtremeEquityReciprocalTerm 1 2 1 = 2 ∧
      printedExtremeEquityReciprocalTerm 1 2 1 ≠
        costConsistentExtremeEquityReciprocalTerm 1 2 1 := by
  norm_num [printedExtremeEquityReciprocalTerm,
    costConsistentExtremeEquityReciprocalTerm]

/-! ## One-category, two-Borough endpoint algebra -/

/-- Efficiency loss at the Borough-specific efficiency endpoint. -/
def twoBoroughEfficientEfficiencyLoss
    (alpha slack u v : ℝ) : ℝ :=
  alpha / slack * (u + v) ^ 2

/-- Efficiency loss at the Borough-specific equity endpoint. -/
def twoBoroughEquitableEfficiencyLoss
    (alpha slack u v : ℝ) : ℝ :=
  2 * alpha / slack * (u ^ 2 + v ^ 2)

/-- Efficiency loss at the one-category pooled efficiency endpoint. -/
def twoBoroughPooledEfficiencyLoss
    (alpha slack u v : ℝ) : ℝ :=
  alpha / slack * (u ^ 2 + v ^ 2)

/-- Borough 1 cost at the Borough-specific efficiency endpoint. -/
def twoBoroughEfficientBoroughOneCost
    (alpha slack u v : ℝ) : ℝ :=
  alpha / slack * u * (u + v)

/-- Borough 2 cost at the Borough-specific efficiency endpoint. -/
def twoBoroughEfficientBoroughTwoCost
    (alpha slack u v : ℝ) : ℝ :=
  alpha / slack * v * (u + v)

/-- Equity loss (the larger Borough cost) at the efficiency endpoint. -/
def twoBoroughEfficientEquityLoss
    (alpha slack u v : ℝ) : ℝ :=
  max (twoBoroughEfficientBoroughOneCost alpha slack u v)
    (twoBoroughEfficientBoroughTwoCost alpha slack u v)

/-- Equity loss at the equal-cost equity endpoint. -/
def twoBoroughEquitableEquityLoss
    (alpha slack u v : ℝ) : ℝ :=
  alpha / slack * (u ^ 2 + v ^ 2)

/-- Price of equity: equitable-endpoint efficiency loss minus efficient loss. -/
def twoBoroughPriceOfEquity (alpha slack u v : ℝ) : ℝ :=
  twoBoroughEquitableEfficiencyLoss alpha slack u v -
    twoBoroughEfficientEfficiencyLoss alpha slack u v

/-- Price of efficiency: efficient-endpoint equity loss minus equitable loss. -/
def twoBoroughPriceOfEfficiency (alpha slack u v : ℝ) : ℝ :=
  twoBoroughEfficientEquityLoss alpha slack u v -
    twoBoroughEquitableEquityLoss alpha slack u v

/-- Gain from replacing the two Borough-specific queues by the pooled queue. -/
def twoBoroughPoolingGain (alpha slack u v : ℝ) : ℝ :=
  twoBoroughEfficientEfficiencyLoss alpha slack u v -
    twoBoroughPooledEfficiencyLoss alpha slack u v

/-- Price of equity minus the analytical pooling gain. -/
def twoBoroughPriceMinusPooling (alpha slack u v : ℝ) : ℝ :=
  twoBoroughPriceOfEquity alpha slack u v -
    twoBoroughPoolingGain alpha slack u v

/--
Current-draft Price of Equity identity, with `u = sqrt (lambda_1 r_1)` and
`v = sqrt (lambda_2 r_2)`.
-/
theorem twoBorough_priceOfEquity_eq
    (alpha slack u v : ℝ) (_hslack : 0 < slack) :
    twoBoroughPriceOfEquity alpha slack u v =
      alpha / slack * (u - v) ^ 2 := by
  unfold twoBoroughPriceOfEquity twoBoroughEquitableEfficiencyLoss
    twoBoroughEfficientEfficiencyLoss
  ring

/-- The current-draft Price of Equity is nonnegative for positive `alpha` and slack. -/
theorem twoBorough_priceOfEquity_nonneg
    {alpha slack u v : ℝ} (halpha : 0 ≤ alpha) (hslack : 0 < slack) :
    0 ≤ twoBoroughPriceOfEquity alpha slack u v := by
  rw [twoBorough_priceOfEquity_eq alpha slack u v hslack]
  positivity

/-- Under the square-root ordering `v ≤ u`, Borough 1 has the larger endpoint cost. -/
theorem twoBoroughEfficientBoroughTwoCost_le_one
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ u) :
    twoBoroughEfficientBoroughTwoCost alpha slack u v ≤
      twoBoroughEfficientBoroughOneCost alpha slack u v := by
  apply sub_nonneg.mp
  have hscale : 0 ≤ alpha / slack :=
    div_nonneg halpha hslack.le
  have hfactor : 0 ≤ (u - v) * (u + v) :=
    mul_nonneg (sub_nonneg.mpr huv) (add_nonneg hu hv)
  have hidentity :
      twoBoroughEfficientBoroughOneCost alpha slack u v -
          twoBoroughEfficientBoroughTwoCost alpha slack u v =
        (alpha / slack) * ((u - v) * (u + v)) := by
    unfold twoBoroughEfficientBoroughOneCost
      twoBoroughEfficientBoroughTwoCost
    ring
  rw [hidentity]
  exact mul_nonneg hscale hfactor

/-- With `v ≤ u`, the max in the efficient endpoint's equity loss is Borough 1. -/
theorem twoBoroughEfficientEquityLoss_eq_one
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ u) :
    twoBoroughEfficientEquityLoss alpha slack u v =
      twoBoroughEfficientBoroughOneCost alpha slack u v := by
  unfold twoBoroughEfficientEquityLoss
  exact max_eq_left
    (twoBoroughEfficientBoroughTwoCost_le_one halpha hslack hu hv huv)

/--
Current-draft Price of Efficiency identity under
`sqrt (lambda_1 r_1) = u ≥ v = sqrt (lambda_2 r_2)`.
-/
theorem twoBorough_priceOfEfficiency_eq_of_v_le_u
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ u) :
    twoBoroughPriceOfEfficiency alpha slack u v =
      alpha / slack * v * (u - v) := by
  unfold twoBoroughPriceOfEfficiency
  rw [twoBoroughEfficientEquityLoss_eq_one halpha hslack hu hv huv]
  unfold twoBoroughEfficientBoroughOneCost
    twoBoroughEquitableEquityLoss
  ring

/-- The Price of Efficiency formula is nonnegative under the source ordering. -/
theorem twoBorough_priceOfEfficiency_nonneg_of_v_le_u
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : v ≤ u) :
    0 ≤ twoBoroughPriceOfEfficiency alpha slack u v := by
  rw [twoBorough_priceOfEfficiency_eq_of_v_le_u halpha hslack hu hv huv]
  exact mul_nonneg
    (mul_nonneg (div_nonneg halpha hslack.le) hv)
    (sub_nonneg.mpr huv)

/-- The two-Borough analytical pooling gain is `2 * alpha * u * v / slack`. -/
theorem twoBorough_poolingGain_eq
    (alpha slack u v : ℝ) (_hslack : 0 < slack) :
    twoBoroughPoolingGain alpha slack u v =
      2 * alpha * u * v / slack := by
  unfold twoBoroughPoolingGain twoBoroughEfficientEfficiencyLoss
    twoBoroughPooledEfficiencyLoss
  ring

/-- The analytical pooling gain is nonnegative for nonnegative square-root loads. -/
theorem twoBorough_poolingGain_nonneg
    {alpha slack u v : ℝ}
    (halpha : 0 ≤ alpha) (hslack : 0 < slack)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ twoBoroughPoolingGain alpha slack u v := by
  rw [twoBorough_poolingGain_eq alpha slack u v hslack]
  positivity

/--
The exact comparison in the current draft: Price of Equity minus pooling gain.
Its sign depends on the relative magnitudes of `u` and `v`.
-/
theorem twoBorough_priceMinusPooling_eq
    (alpha slack u v : ℝ) (_hslack : 0 < slack) :
    twoBoroughPriceMinusPooling alpha slack u v =
      alpha / slack * ((u - v) ^ 2 - 2 * u * v) := by
  unfold twoBoroughPriceMinusPooling twoBoroughPriceOfEquity
    twoBoroughPoolingGain twoBoroughEquitableEfficiencyLoss
    twoBoroughEfficientEfficiencyLoss twoBoroughPooledEfficiencyLoss
  ring

/-- At equal square-root loads, pooling gain is strictly larger than Price of Equity. -/
theorem twoBorough_poolingGain_gt_priceOfEquity_counterexample :
    twoBoroughPriceOfEquity 1 1 1 1 < twoBoroughPoolingGain 1 1 1 1 := by
  norm_num [twoBoroughPriceOfEquity, twoBoroughPoolingGain,
    twoBoroughEquitableEfficiencyLoss, twoBoroughEfficientEfficiencyLoss,
    twoBoroughPooledEfficiencyLoss]

/-- At sufficiently unequal square-root loads, Price of Equity exceeds pooling gain. -/
theorem twoBorough_priceOfEquity_gt_poolingGain_counterexample :
    twoBoroughPoolingGain 1 1 4 1 < twoBoroughPriceOfEquity 1 1 4 1 := by
  norm_num [twoBoroughPriceOfEquity, twoBoroughPoolingGain,
    twoBoroughEquitableEfficiencyLoss, twoBoroughEfficientEfficiencyLoss,
    twoBoroughPooledEfficiencyLoss]

end

end LG24ServiceLevelAgreements
