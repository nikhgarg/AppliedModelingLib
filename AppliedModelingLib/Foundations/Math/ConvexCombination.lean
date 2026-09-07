import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field

namespace AppliedModelingLib

/-!
# Two-Point Convex Combination Algebra

Reusable real-line algebra for paper arguments that compare one component to a
two-group weighted mixture.

## Main declarations

- `right_lt_weightedAverage_of_right_lt_left`
- `weighted_share_lt_weight_of_value_lt_total`
- `twoPointWeightedAverage`
- `weightedAverage_lt_right_of_left_lt_right`
- `lt_twoPointWeightedAverage_of_lt_components`
- `lt_twoPointWeightedAverage_of_weighted_gap_pos`
- `gatedTwoPointWeightedAverage`
- `continuous_gatedTwoPointWeightedAverage`
- `continuous_twoPointWeightedAverage`
-/

/--
The weighted average of two real components with arbitrary real weights.  Most
paper uses provide nonnegative weights and a positive denominator separately.
-/
noncomputable def twoPointWeightedAverage
    (weightLeft weightRight left right : ℝ) : ℝ :=
  (weightLeft * left + weightRight * right) / (weightLeft + weightRight)

/--
If the right endpoint is strictly below the left endpoint and the right weight
is less than one, then the two-point weighted average lies strictly above the
right endpoint.
-/
theorem right_lt_weightedAverage_of_right_lt_left
    {weightRight left right : ℝ}
    (hweight_lt_one : weightRight < 1)
    (hright_lt_left : right < left) :
    right < (1 - weightRight) * left + weightRight * right := by
  have hleft_weight_pos : 0 < 1 - weightRight := by
    linarith
  have hgap_pos : 0 < left - right := sub_pos.mpr hright_lt_left
  have hprod_pos : 0 < (1 - weightRight) * (left - right) :=
    mul_pos hleft_weight_pos hgap_pos
  nlinarith

/--
If a component value is strictly below the total and the component weight and
total are positive, then its normalized share is strictly below its weight.
-/
theorem weighted_share_lt_weight_of_value_lt_total
    {weight value total : ℝ}
    (hweight_pos : 0 < weight)
    (htotal_pos : 0 < total)
    (hvalue_lt_total : value < total) :
    weight * value / total < weight := by
  rw [div_lt_iff₀ htotal_pos]
  nlinarith [mul_pos hweight_pos (sub_pos.mpr hvalue_lt_total)]

/--
If a two-state weighted average gives positive weight to a strictly lower left
component and the two weights sum to one, then the average is strictly below
the right component.
-/
theorem weightedAverage_lt_right_of_left_lt_right
    {weightLeft weightRight left right : ℝ}
    (hleft_weight_pos : 0 < weightLeft)
    (hsum : weightLeft + weightRight = 1)
    (hleft_lt_right : left < right) :
    weightLeft * left + weightRight * right < right := by
  have hgap_pos : 0 < right - left := sub_pos.mpr hleft_lt_right
  have hproduct_pos : 0 < weightLeft * (right - left) :=
    mul_pos hleft_weight_pos hgap_pos
  have hrewrite :
      weightLeft * left + weightRight * right =
        right - weightLeft * (right - left) := by
    have hright_weight : weightRight = 1 - weightLeft := by
      linarith
    rw [hright_weight]
    ring
  rw [hrewrite]
  linarith

/--
If a two-state weighted average gives positive weight to a strictly higher
right component and the two weights sum to one, then the average is strictly
above the left component.
-/
theorem left_lt_weightedAverage_of_left_lt_right
    {weightLeft weightRight left right : ℝ}
    (hright_weight_pos : 0 < weightRight)
    (hsum : weightLeft + weightRight = 1)
    (hleft_lt_right : left < right) :
    left < weightLeft * left + weightRight * right := by
  have hgap_pos : 0 < right - left := sub_pos.mpr hleft_lt_right
  have hproduct_pos : 0 < weightRight * (right - left) :=
    mul_pos hright_weight_pos hgap_pos
  have hrewrite :
      weightLeft * left + weightRight * right =
        left + weightRight * (right - left) := by
    have hleft_weight : weightLeft = 1 - weightRight := by
      linarith
    rw [hleft_weight]
    ring
  rw [hrewrite]
  linarith

/-- A positive left weight and nonnegative right weight give a positive sum. -/
theorem twoPointWeightedAverage_denominator_pos_of_left_pos_right_nonneg
    {weightLeft weightRight : ℝ}
    (hleft_pos : 0 < weightLeft) (hright_nonneg : 0 ≤ weightRight) :
    0 < weightLeft + weightRight := by
  linarith

/--
Two-point weighted average where the right component is present only through a
nonnegative gate.  The weights are `(1 - share)` for the left component and
`share * gate` for the right component.
-/
noncomputable def gatedTwoPointWeightedAverage
    (share gate left right : ℝ) : ℝ :=
  twoPointWeightedAverage (1 - share) (share * gate) left right

/--
The denominator of a gated two-point average is positive when the base share is
below one and the gated component has nonnegative mass.
-/
theorem gatedTwoPointWeightedAverage_denominator_pos
    {share gate : ℝ} (hshare_nonneg : 0 ≤ share)
    (hshare_lt_one : share < 1) (hgate_nonneg : 0 ≤ gate) :
    0 < (1 - share) + share * gate :=
  twoPointWeightedAverage_denominator_pos_of_left_pos_right_nonneg
    (by linarith) (mul_nonneg hshare_nonneg hgate_nonneg)

/--
If both components are strictly above a target, with positive total weight and
nonnegative component weights, then their two-point weighted average is above
the target.
-/
theorem lt_twoPointWeightedAverage_of_lt_components
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hleft_weight_pos : 0 < weightLeft)
    (hright_weight_nonneg : 0 ≤ weightRight)
    (hleft : target < left)
    (hright : target < right) :
    target <
      twoPointWeightedAverage weightLeft weightRight left right := by
  have hnum :
      (weightLeft + weightRight) * target <
        weightLeft * left + weightRight * right := by
    have h0 : weightLeft * target < weightLeft * left :=
      mul_lt_mul_of_pos_left hleft hleft_weight_pos
    have h1 : weightRight * target ≤ weightRight * right :=
      mul_le_mul_of_nonneg_left hright.le hright_weight_nonneg
    nlinarith
  calc
    target = ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]
    _ < (weightLeft * left + weightRight * right) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = twoPointWeightedAverage weightLeft weightRight left right := by
      rfl

/--
If both components are strictly below a target, with positive total weight and
nonnegative component weights, then their two-point weighted average is below
the target.
-/
theorem twoPointWeightedAverage_lt_of_components_lt
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hleft_weight_pos : 0 < weightLeft)
    (hright_weight_nonneg : 0 ≤ weightRight)
    (hleft : left < target)
    (hright : right < target) :
    twoPointWeightedAverage weightLeft weightRight left right <
      target := by
  have hnum :
      weightLeft * left + weightRight * right <
        (weightLeft + weightRight) * target := by
    have h0 : weightLeft * left < weightLeft * target :=
      mul_lt_mul_of_pos_left hleft hleft_weight_pos
    have h1 : weightRight * right ≤ weightRight * target :=
      mul_le_mul_of_nonneg_left hright.le hright_weight_nonneg
    nlinarith
  calc
    twoPointWeightedAverage weightLeft weightRight left right =
        (weightLeft * left + weightRight * right) /
          (weightLeft + weightRight) := by
      rfl
    _ < ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = target := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]

/--
Weighted-gap form: if the weighted sum of component gaps above the target is
positive, then the weighted average is above the target.
-/
theorem lt_twoPointWeightedAverage_of_weighted_gap_pos
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hgap :
      0 <
        weightLeft * (left - target) +
          weightRight * (right - target)) :
    target <
      twoPointWeightedAverage weightLeft weightRight left right := by
  have hnum :
      (weightLeft + weightRight) * target <
        weightLeft * left + weightRight * right := by
    nlinarith
  calc
    target = ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]
    _ < (weightLeft * left + weightRight * right) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = twoPointWeightedAverage weightLeft weightRight left right := by
      rfl

/--
Weighted-gap form: if the weighted sum of component gaps above the target is
negative, then the weighted average is below the target.
-/
theorem twoPointWeightedAverage_lt_of_weighted_gap_neg
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hgap :
      weightLeft * (left - target) +
          weightRight * (right - target) <
        0) :
    twoPointWeightedAverage weightLeft weightRight left right <
      target := by
  have hnum :
      weightLeft * left + weightRight * right <
        (weightLeft + weightRight) * target := by
    nlinarith
  calc
    twoPointWeightedAverage weightLeft weightRight left right =
        (weightLeft * left + weightRight * right) /
          (weightLeft + weightRight) := by
      rfl
    _ < ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = target := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]

/--
If both components of a gated two-point average are strictly above a target,
then the gated average is above that target.
-/
theorem lt_gatedTwoPointWeightedAverage_of_lt_components
    {share gate left right target : ℝ}
    (hshare_nonneg : 0 ≤ share) (hshare_lt_one : share < 1)
    (hgate_nonneg : 0 ≤ gate)
    (hleft : target < left) (hright : target < right) :
    target < gatedTwoPointWeightedAverage share gate left right := by
  exact
    lt_twoPointWeightedAverage_of_lt_components
      (gatedTwoPointWeightedAverage_denominator_pos
        hshare_nonneg hshare_lt_one hgate_nonneg)
      (by linarith)
      (mul_nonneg hshare_nonneg hgate_nonneg)
      hleft hright

/--
If the weighted component gap above a target is positive, then the gated
two-point average is above that target.
-/
theorem lt_gatedTwoPointWeightedAverage_of_weighted_gap_pos
    {share gate left right target : ℝ}
    (hshare_nonneg : 0 ≤ share) (hshare_lt_one : share < 1)
    (hgate_nonneg : 0 ≤ gate)
    (hgap :
      0 <
        (1 - share) * (left - target) +
          (share * gate) * (right - target)) :
    target < gatedTwoPointWeightedAverage share gate left right :=
  lt_twoPointWeightedAverage_of_weighted_gap_pos
    (gatedTwoPointWeightedAverage_denominator_pos
      hshare_nonneg hshare_lt_one hgate_nonneg)
    hgap

/--
If both components of a gated two-point average are strictly below a target,
then the gated average is below that target.
-/
theorem gatedTwoPointWeightedAverage_lt_of_components_lt
    {share gate left right target : ℝ}
    (hshare_nonneg : 0 ≤ share) (hshare_lt_one : share < 1)
    (hgate_nonneg : 0 ≤ gate)
    (hleft : left < target) (hright : right < target) :
    gatedTwoPointWeightedAverage share gate left right < target := by
  exact
    twoPointWeightedAverage_lt_of_components_lt
      (gatedTwoPointWeightedAverage_denominator_pos
        hshare_nonneg hshare_lt_one hgate_nonneg)
      (by linarith)
      (mul_nonneg hshare_nonneg hgate_nonneg)
      hleft hright

/--
If the weighted component gap above a target is negative, then the gated
two-point average is below that target.
-/
theorem gatedTwoPointWeightedAverage_lt_of_weighted_gap_neg
    {share gate left right target : ℝ}
    (hshare_nonneg : 0 ≤ share) (hshare_lt_one : share < 1)
    (hgate_nonneg : 0 ≤ gate)
    (hgap :
      (1 - share) * (left - target) +
          (share * gate) * (right - target) <
        0) :
    gatedTwoPointWeightedAverage share gate left right < target :=
  twoPointWeightedAverage_lt_of_weighted_gap_neg
    (gatedTwoPointWeightedAverage_denominator_pos
      hshare_nonneg hshare_lt_one hgate_nonneg)
    hgap

/-- Continuity of a two-point weighted average with nonzero denominator. -/
theorem continuous_twoPointWeightedAverage
    {α : Type*} [TopologicalSpace α]
    {weightLeft weightRight left right : α → ℝ}
    (hweightLeft : Continuous weightLeft)
    (hweightRight : Continuous weightRight)
    (hleft : Continuous left)
    (hright : Continuous right)
    (hdenom : ∀ x, weightLeft x + weightRight x ≠ 0) :
    Continuous (fun x : α =>
      twoPointWeightedAverage
        (weightLeft x) (weightRight x) (left x) (right x)) := by
  unfold twoPointWeightedAverage
  exact ((hweightLeft.mul hleft).add (hweightRight.mul hright)).div
    (hweightLeft.add hweightRight) hdenom

/--
Continuity of a gated two-point average with a fixed share, fixed left
component, and continuous gate/right component.
-/
theorem continuous_gatedTwoPointWeightedAverage
    {α : Type*} [TopologicalSpace α]
    {share left : ℝ} {gate right : α → ℝ}
    (hshare_nonneg : 0 ≤ share) (hshare_lt_one : share < 1)
    (hgate_nonneg : ∀ x, 0 ≤ gate x)
    (hgate : Continuous gate) (hright : Continuous right) :
    Continuous (fun x : α =>
      gatedTwoPointWeightedAverage share (gate x) left (right x)) := by
  have hdenom :
      ∀ x : α, (1 - share) + share * gate x ≠ 0 := by
    intro x
    exact ne_of_gt
      (gatedTwoPointWeightedAverage_denominator_pos
        hshare_nonneg hshare_lt_one (hgate_nonneg x))
  simpa [gatedTwoPointWeightedAverage]
    using
      continuous_twoPointWeightedAverage
        (weightLeft := fun _ : α => 1 - share)
        (weightRight := fun x : α => share * gate x)
        (left := fun _ : α => left)
        (right := right)
        continuous_const (continuous_const.mul hgate) continuous_const
        hright hdenom

/--
For a positive constant `a`, the ratio `x / (a + x)` is strictly increasing on
nonnegative `x`.
-/
theorem div_const_add_lt_div_const_add
    {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hxy : x < y) :
    x / (a + x) < y / (a + y) := by
  have hdenx : 0 < a + x := by
    linarith
  have hdeny : 0 < a + y := by
    linarith
  rw [div_lt_div_iff₀ hdenx hdeny]
  nlinarith [mul_pos ha (sub_pos.mpr hxy)]

end AppliedModelingLib
