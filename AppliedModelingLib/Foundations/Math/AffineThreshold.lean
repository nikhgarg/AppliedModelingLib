import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import AppliedModelingLib.Foundations.Math.ThresholdCharacterization

/-!
# Affine Thresholds

Reusable one-dimensional threshold algebra for positive-slope affine scores.

## Main declarations

- `affineCutoff`
- `threshold_le_affine_iff_cutoff_le`
- `affine_le_threshold_iff_le_cutoff`
- `lowerCutoffStrategy_of_affine_threshold`
- `affine_strictMono`
- `lowerThresholdCutoff_unique`
- `affine_div_le_affine_div_of_le`
- `affine_div_lt_affine_div_of_lt`
- `indexed_affineDecreasing_regularities_Icc`
- `exists_affine_lt`
- `exists_lt_affine`
- `exists_affine_lt_before`
- `exists_lt_affine_after`
-/

namespace AppliedModelingLib

noncomputable section

/-- Cutoff in the input variable for a positive-slope affine score. -/
def affineCutoff (intercept slope threshold : ℝ) : ℝ :=
  (threshold - intercept) / slope

/--
A positive-slope affine score exceeds a threshold exactly above the induced
cutoff.
-/
theorem threshold_le_affine_iff_cutoff_le
    {intercept slope threshold x : ℝ} (hslope : 0 < slope) :
    threshold ≤ intercept + slope * x ↔
      affineCutoff intercept slope threshold ≤ x := by
  unfold affineCutoff
  constructor
  · intro h
    have hsub : threshold - intercept ≤ slope * x := by
      linarith
    rw [div_le_iff₀ hslope]
    simpa [mul_comm] using hsub
  · intro h
    have hmul : threshold - intercept ≤ slope * x := by
      have := (div_le_iff₀ hslope).mp h
      simpa [mul_comm] using this
    linarith

/--
A positive-slope affine threshold comparison is a lower-cutoff rule in the
input variable.
-/
theorem lowerCutoffStrategy_of_affine_threshold
    {intercept slope threshold : ℝ} (hslope : 0 < slope) :
    LowerCutoffStrategy
      (fun value : ℝ => threshold ≤ intercept + slope * value) := by
  refine ⟨affineCutoff intercept slope threshold, ?_⟩
  intro value
  exact threshold_le_affine_iff_cutoff_le hslope

/--
A positive-slope affine score is below a threshold exactly below the induced
cutoff.
-/
theorem affine_le_threshold_iff_le_cutoff
    {intercept slope threshold x : ℝ} (hslope : 0 < slope) :
    intercept + slope * x ≤ threshold ↔
      x ≤ affineCutoff intercept slope threshold := by
  unfold affineCutoff
  constructor
  · intro h
    have hsub : slope * x ≤ threshold - intercept := by
      linarith
    rw [le_div_iff₀ hslope]
    simpa [mul_comm] using hsub
  · intro h
    have hmul : slope * x ≤ threshold - intercept := by
      have := (le_div_iff₀ hslope).mp h
      simpa [mul_comm] using this
    linarith

/-- A positive-slope affine score is strictly increasing. -/
theorem affine_strictMono (intercept : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    StrictMono (fun x : ℝ => intercept + slope * x) := by
  intro x y hxy
  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left (mul_lt_mul_of_pos_left hxy hslope) intercept

/--
An indexed positive-slope decreasing affine family is continuous and strictly
antitone on each indexed closed interval.
-/
theorem indexed_affineDecreasing_regularities_Icc
    {ι : Type*} {left right : ι → ℝ}
    (intercept slope : ι → ℝ) (hslope : ∀ i, 0 < slope i) :
    (∀ i,
      ContinuousOn (fun c => intercept i - slope i * c)
        (Set.Icc (left i) (right i))) ∧
      (∀ i,
        StrictAntiOn (fun c => intercept i - slope i * c)
          (Set.Icc (left i) (right i))) := by
  constructor
  · intro i
    exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  · intro i x _hx y _hy hxy
    have hmul : slope i * x < slope i * y :=
      mul_lt_mul_of_pos_left hxy (hslope i)
    nlinarith

/--
A positive-slope affine score divided by a positive denominator is weakly
increasing.
-/
theorem affine_div_le_affine_div_of_le
    {intercept slope denom x y : ℝ}
    (hslope : 0 ≤ slope) (hdenom : 0 < denom) (hxy : x ≤ y) :
    (intercept + slope * x) / denom ≤
      (intercept + slope * y) / denom := by
  have hnum :
      intercept + slope * x ≤ intercept + slope * y := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left hxy hslope) intercept
  exact div_le_div_of_nonneg_right hnum hdenom.le

/--
A positive-slope affine score divided by a positive denominator is strictly
increasing.
-/
theorem affine_div_lt_affine_div_of_lt
    {intercept slope denom x y : ℝ}
    (hslope : 0 < slope) (hdenom : 0 < denom) (hxy : x < y) :
    (intercept + slope * x) / denom <
      (intercept + slope * y) / denom := by
  have hnum :
      intercept + slope * x < intercept + slope * y := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_lt_add_left (mul_lt_mul_of_pos_left hxy hslope) intercept
  exact div_lt_div_of_pos_right hnum hdenom

/--
A positive-slope affine score divided by a positive denominator preserves and
reflects weak order.
-/
theorem affine_div_le_affine_div_iff
    {intercept slope denom x y : ℝ}
    (hslope : 0 < slope) (hdenom : 0 < denom) :
    (intercept + slope * x) / denom ≤
        (intercept + slope * y) / denom ↔
      x ≤ y := by
  constructor
  · intro hle
    by_contra hnot
    have hlt : y < x := lt_of_not_ge hnot
    exact not_lt_of_ge hle
      (affine_div_lt_affine_div_of_lt hslope hdenom hlt)
  · intro hxy
    exact affine_div_le_affine_div_of_le hslope.le hdenom hxy

/--
If twice an affine numerator equals the denominator, then the corresponding
normalized affine value is one half.
-/
theorem half_eq_affine_div_of_two_mul_affine_eq_denom
    {intercept slope denom x : ℝ}
    (hdenom_ne : denom ≠ 0)
    (hcenter : 2 * (intercept + slope * x) = denom) :
    (1 / 2 : ℝ) = (intercept + slope * x) / denom := by
  have hn_ne : intercept + slope * x ≠ 0 := by
    intro hn
    apply hdenom_ne
    rw [← hcenter, hn]
    norm_num
  rw [← hcenter]
  field_simp [hn_ne]

/--
An affine intercept of `denom / 2 - slope * x` makes twice the affine numerator
at `x` equal to the denominator.
-/
theorem two_mul_affine_eq_denom_of_intercept_eq_half_denom_sub_slope_mul
    {intercept slope denom x : ℝ}
    (hintercept : intercept = denom / 2 - slope * x) :
    2 * (intercept + slope * x) = denom := by
  rw [hintercept]
  ring

/--
The base-term form of the preceding two lemmas: the affine value at `x`,
normalized by a nonzero denominator, is one half.
-/
theorem half_eq_affine_div_of_intercept_eq_half_denom_sub_slope_mul
    {intercept slope denom x : ℝ}
    (hdenom_ne : denom ≠ 0)
    (hintercept : intercept = denom / 2 - slope * x) :
    (1 / 2 : ℝ) = (intercept + slope * x) / denom :=
  half_eq_affine_div_of_two_mul_affine_eq_denom
    hdenom_ne
    (two_mul_affine_eq_denom_of_intercept_eq_half_denom_sub_slope_mul
      hintercept)

/--
A lower-threshold predicate on the real line has a unique cutoff: if two
cutoffs generate the same weak upper ray, then the cutoffs are equal.
-/
theorem lowerThresholdCutoff_unique {cutoff₁ cutoff₂ : ℝ}
    (h : ∀ x : ℝ, cutoff₁ ≤ x ↔ cutoff₂ ≤ x) :
    cutoff₁ = cutoff₂ := by
  apply le_antisymm
  · exact (h cutoff₂).2 le_rfl
  · exact (h cutoff₁).1 le_rfl

/-- A positive-slope affine score eventually falls below any finite level. -/
theorem exists_affine_lt (intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, intercept + slope * x < threshold := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  refine ⟨cutoff - 1, ?_⟩
  have hnot_cutoff : ¬ cutoff ≤ cutoff - 1 := by
    linarith
  have hnot_threshold :
      ¬ threshold ≤ intercept + slope * (cutoff - 1) := by
    intro h
    exact hnot_cutoff
      ((threshold_le_affine_iff_cutoff_le (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := cutoff - 1)
        hslope).1 h)
  exact lt_of_not_ge hnot_threshold

/-- A positive-slope affine score eventually exceeds any finite level. -/
theorem exists_lt_affine (intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, threshold < intercept + slope * x := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  refine ⟨cutoff + 1, ?_⟩
  have hnot_cutoff : ¬ cutoff + 1 ≤ cutoff := by
    linarith
  have hnot_affine :
      ¬ intercept + slope * (cutoff + 1) ≤ threshold := by
    intro h
    exact hnot_cutoff
      ((affine_le_threshold_iff_le_cutoff (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := cutoff + 1)
        hslope).1 h)
  exact lt_of_not_ge hnot_affine

/-- A positive-slope affine score falls below any finite level before any finite bound. -/
theorem exists_affine_lt_before (upper intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, x < upper ∧ intercept + slope * x < threshold := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  let x : ℝ := min upper cutoff - 1
  have hx_upper : x < upper := by
    dsimp [x]
    exact (sub_lt_self _ zero_lt_one).trans_le (min_le_left _ _)
  have hx_cutoff : x < cutoff := by
    dsimp [x]
    exact (sub_lt_self _ zero_lt_one).trans_le (min_le_right _ _)
  have hnot_threshold :
      ¬ threshold ≤ intercept + slope * x := by
    intro h
    have hcutoff_le_x :
        affineCutoff intercept slope threshold ≤ x :=
      (threshold_le_affine_iff_cutoff_le (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := x) hslope).1 h
    linarith
  exact ⟨x, hx_upper, lt_of_not_ge hnot_threshold⟩

/-- A positive-slope affine score exceeds any finite level after any finite bound. -/
theorem exists_lt_affine_after (lower intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, lower < x ∧ threshold < intercept + slope * x := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  let x : ℝ := max lower cutoff + 1
  have hlower_x : lower < x := by
    dsimp [x]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hcutoff_x : cutoff < x := by
    dsimp [x]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hnot_affine :
      ¬ intercept + slope * x ≤ threshold := by
    intro h
    have hx_le_cutoff :
        x ≤ affineCutoff intercept slope threshold :=
      (affine_le_threshold_iff_le_cutoff (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := x) hslope).1 h
    linarith
  exact ⟨x, hlower_x, lt_of_not_ge hnot_affine⟩

end

end AppliedModelingLib
