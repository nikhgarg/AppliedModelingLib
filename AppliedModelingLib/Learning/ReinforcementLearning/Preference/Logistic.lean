import AppliedModelingLib.Learning.ReinforcementLearning.Preference.UtilityComparison
import Mathlib.Tactic

/-!
# The logistic comparison link

This finite-dimensional preference layer uses the standard logistic link and
the elementary bounds needed to compare logistic objective gaps with score
gaps on the unit interval.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The Bradley--Terry--Luce logistic comparison link. -/
noncomputable def logisticLink (difference : ℝ) : ℝ :=
  (1 + Real.exp (-difference))⁻¹

/-- The logistic link is normalized at an equal score. -/
theorem logisticLink_zero : logisticLink 0 = 1 / 2 := by
  norm_num [logisticLink]

/-- Logistic comparisons of opposite score differences are complementary. -/
theorem logisticLink_add_neg (difference : ℝ) :
    logisticLink difference + logisticLink (-difference) = 1 := by
  unfold logisticLink
  rw [Real.exp_neg]
  field_simp
  ring

/-- The Bradley--Terry--Luce logistic link is strictly increasing on the
whole real line.  This is the order fact used to transfer a score maximizer
to the paper's alternative preference objective. -/
theorem strictMono_logisticLink : StrictMono logisticLink := by
  intro first second hfirstSecond
  unfold logisticLink
  apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
  gcongr

/-- Writing a logistic score difference as the corresponding exponential ratio. -/
theorem logisticLink_scoreDifference_eq_exponentialRatio {Trajectory : Type*}
    (score : Trajectory → ℝ) (first second : Trajectory) :
    logisticLink (score first - score second) =
      Real.exp (score first) / (Real.exp (score first) + Real.exp (score second)) := by
  unfold logisticLink
  rw [show -(score first - score second) = score second - score first by ring,
    Real.exp_sub]
  field_simp

/-- The logistic excess over one half as an exponential-score fraction. -/
theorem logisticLink_sub_half_eq_exponentialFraction (difference : ℝ) :
    logisticLink difference - 1 / 2 =
      (Real.exp difference - 1) / (2 * (Real.exp difference + 1)) := by
  unfold logisticLink
  rw [Real.exp_neg]
  have hpositive : Real.exp difference ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp [hpositive]
  ring

/-- On `[0,1]`, the logistic gain above one half has the stated linear lower bound. -/
theorem linear_lowerBound_logisticLink_sub_half {difference : ℝ}
    (hnonneg : 0 ≤ difference) (hone : difference ≤ 1) :
    difference / (2 * (Real.exp 1 + 1)) ≤ logisticLink difference - 1 / 2 := by
  rw [show logisticLink difference - 1 / 2 =
      (Real.exp difference - 1) / (2 * (Real.exp difference + 1)) by
    unfold logisticLink
    rw [Real.exp_neg]
    field_simp
    ring]
  have hexpLower : difference ≤ Real.exp difference - 1 := by
    linarith [Real.add_one_le_exp difference]
  have hnum : 0 ≤ Real.exp difference - 1 := hnonneg.trans hexpLower
  have hdenPos : 0 < 2 * (Real.exp difference + 1) := by positivity
  have hdenOrder : 2 * (Real.exp difference + 1) ≤ 2 * (Real.exp 1 + 1) := by
    gcongr
  calc
    difference / (2 * (Real.exp 1 + 1)) ≤
        (Real.exp difference - 1) / (2 * (Real.exp 1 + 1)) :=
      div_le_div_of_nonneg_right hexpLower (by positivity)
    _ ≤ (Real.exp difference - 1) / (2 * (Real.exp difference + 1)) :=
      div_le_div_of_nonneg_left hnum hdenPos hdenOrder

/-- For a nonnegative score difference, the logistic gain above one half is
at most half the score difference. -/
theorem logisticLink_sub_half_le_linear {difference : ℝ} (hnonneg : 0 ≤ difference) :
    logisticLink difference - 1 / 2 ≤ difference / 2 := by
  rw [show logisticLink difference - 1 / 2 =
      (Real.exp difference - 1) / (2 * (Real.exp difference + 1)) by
    unfold logisticLink
    rw [Real.exp_neg]
    field_simp
    ring]
  have hlinearAtNeg := Real.add_one_le_exp (-difference)
  have hexpPos : 0 < Real.exp difference := Real.exp_pos difference
  have hproduct := mul_le_mul_of_nonneg_left hlinearAtNeg hexpPos.le
  have hinverse : Real.exp difference * Real.exp (-difference) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hinverse] at hproduct
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The two-sided linear bounds for a score difference in the unit interval. -/
theorem linear_bounds_logisticLink_sub_half {difference : ℝ}
    (hnonneg : 0 ≤ difference) (hone : difference ≤ 1) :
    difference / (2 * (Real.exp 1 + 1)) ≤ logisticLink difference - 1 / 2 ∧
      logisticLink difference - 1 / 2 ≤ difference / 2 :=
  ⟨linear_lowerBound_logisticLink_sub_half hnonneg hone,
    logisticLink_sub_half_le_linear hnonneg⟩

end PreferenceRL

end AppliedModelingLib
