import AppliedModelingLib.Queueing.ManyServerBirthDeath
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Polynomial moments of a geometric tail

This module records elementary summation formulas for a geometric tail on the
nonnegative integers.  They are useful whenever a stationary queue has a
constant-ratio tail, independently of any particular asymptotic regime.
-/

namespace AppliedModelingLib.Probability.Queueing

/-- The zeroth through fourth raw power sums of a geometric tail. -/
theorem hasSum_geometric_tail_pow_zero
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => r ^ n) (1 / (1 - r)) := by
  simpa [one_div] using hasSum_geometric_of_lt_one hr_nonneg hr_lt_one

/-- The first raw power sum of a geometric tail. -/
theorem hasSum_geometric_tail_pow_one
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hshift := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr_norm
  have hzero := hasSum_geometric_tail_pow_zero hr_nonneg hr_lt_one
  have hsub := hshift.sub hzero
  convert hsub using 1
  · ext n
    norm_num [Nat.choose_one_right]
    ring
  · have hgap : 1 - r ≠ 0 := by linarith
    field_simp [hgap]
    ring

/-- The second raw power sum of a geometric tail. -/
theorem hasSum_geometric_tail_pow_two
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n)
      (r * (1 + r) / (1 - r) ^ 3) := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hshift := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr_norm
  have hone := hasSum_geometric_tail_pow_one hr_nonneg hr_lt_one
  have hzero := hasSum_geometric_tail_pow_zero hr_nonneg hr_lt_one
  have hlinear := (hshift.mul_left 2).sub (hone.mul_left 3)
  have hsub := hlinear.sub (hzero.mul_left 2)
  convert hsub using 1
  · ext n
    have hchoose : (2 : ℝ) * ((n + 2).choose 2 : ℝ) =
        (n : ℝ) ^ 2 + 3 * n + 2 := by
      have hnat : (n + 2).choose 2 * 2 = (n + 2) * (n + 1) := by
        calc
          (n + 2).choose 2 * 2 = (n + 2).choose 1 * ((n + 2) - 1) :=
            Nat.choose_succ_right_eq (n + 2) 1
          _ = (n + 2) * (n + 1) := by simp [Nat.choose_one_right]
      have hreal : ((n + 2).choose 2 : ℝ) * 2 = (n + 2 : ℝ) * (n + 1) := by
        exact_mod_cast hnat
      calc
        (2 : ℝ) * ((n + 2).choose 2 : ℝ) =
            ((n + 2).choose 2 : ℝ) * 2 := by ring
        _ = (n + 2 : ℝ) * (n + 1) := hreal
        _ = (n : ℝ) ^ 2 + 3 * n + 2 := by ring
    calc
      (n : ℝ) ^ 2 * r ^ n =
          ((2 : ℝ) * ((n + 2).choose 2 : ℝ) - 3 * n - 2) * r ^ n := by
            rw [hchoose]
            ring
      _ = 2 * (((n + 2).choose 2 : ℝ) * r ^ n) -
          3 * ((n : ℝ) * r ^ n) - 2 * r ^ n := by ring
  · have hgap : 1 - r ≠ 0 := by linarith
    field_simp [hgap]
    ring

/-- The third raw power sum of a geometric tail. -/
theorem hasSum_geometric_tail_pow_three
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n)
      (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4) := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hshift := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 3 hr_norm
  have htwo := hasSum_geometric_tail_pow_two hr_nonneg hr_lt_one
  have hone := hasSum_geometric_tail_pow_one hr_nonneg hr_lt_one
  have hzero := hasSum_geometric_tail_pow_zero hr_nonneg hr_lt_one
  have hlinear := (hshift.mul_left 6).sub (htwo.mul_left 6)
  have hlinear' := hlinear.sub (hone.mul_left 11)
  have hsub := hlinear'.sub (hzero.mul_left 6)
  convert hsub using 1
  · ext n
    have hchoose : (6 : ℝ) * ((n + 3).choose 3 : ℝ) =
        (n : ℝ) ^ 3 + 6 * n ^ 2 + 11 * n + 6 := by
      have hthree : (n + 3).choose 3 * 3 = (n + 3).choose 2 * (n + 1) := by
        simpa using Nat.choose_succ_right_eq (n + 3) 2
      have htwo : (n + 3).choose 2 * 2 = (n + 3) * (n + 2) := by
        calc
          (n + 3).choose 2 * 2 = (n + 3).choose 1 * ((n + 3) - 1) :=
            Nat.choose_succ_right_eq (n + 3) 1
          _ = (n + 3) * (n + 2) := by simp [Nat.choose_one_right]
      have hthree_real : ((n + 3).choose 3 : ℝ) * 3 =
          ((n + 3).choose 2 : ℝ) * (n + 1) := by
        exact_mod_cast hthree
      have htwo_real : ((n + 3).choose 2 : ℝ) * 2 =
          (n + 3 : ℝ) * (n + 2) := by
        exact_mod_cast htwo
      calc
        (6 : ℝ) * ((n + 3).choose 3 : ℝ) =
            2 * (((n + 3).choose 3 : ℝ) * 3) := by ring
        _ = 2 * (((n + 3).choose 2 : ℝ) * (n + 1)) := by rw [hthree_real]
        _ = (((n + 3).choose 2 : ℝ) * 2) * (n + 1) := by ring
        _ = ((n + 3 : ℝ) * (n + 2)) * (n + 1) := by rw [htwo_real]
        _ = (n : ℝ) ^ 3 + 6 * n ^ 2 + 11 * n + 6 := by ring
    calc
      (n : ℝ) ^ 3 * r ^ n =
          ((6 : ℝ) * ((n + 3).choose 3 : ℝ) - 6 * n ^ 2 - 11 * n - 6) * r ^ n := by
            rw [hchoose]
            ring
      _ = 6 * (((n + 3).choose 3 : ℝ) * r ^ n) -
          6 * ((n : ℝ) ^ 2 * r ^ n) - 11 * ((n : ℝ) * r ^ n) - 6 * r ^ n := by ring
  · have hgap : 1 - r ≠ 0 := by linarith
    field_simp [hgap]
    ring

/-- The fourth raw power sum of a geometric tail. -/
theorem hasSum_geometric_tail_pow_four
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 4 * r ^ n)
      (r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5) := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt_one
  have hshift := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 4 hr_norm
  have hthree := hasSum_geometric_tail_pow_three hr_nonneg hr_lt_one
  have htwo := hasSum_geometric_tail_pow_two hr_nonneg hr_lt_one
  have hone := hasSum_geometric_tail_pow_one hr_nonneg hr_lt_one
  have hzero := hasSum_geometric_tail_pow_zero hr_nonneg hr_lt_one
  have hlinear := (hshift.mul_left 24).sub (hthree.mul_left 10)
  have hlinear' := hlinear.sub (htwo.mul_left 35)
  have hlinear'' := hlinear'.sub (hone.mul_left 50)
  have hsub := hlinear''.sub (hzero.mul_left 24)
  convert hsub using 1
  · ext n
    have hchoose : (24 : ℝ) * ((n + 4).choose 4 : ℝ) =
        (n : ℝ) ^ 4 + 10 * n ^ 3 + 35 * n ^ 2 + 50 * n + 24 := by
      have hfour : (n + 4).choose 4 * 4 = (n + 4).choose 3 * (n + 1) := by
        simpa using Nat.choose_succ_right_eq (n + 4) 3
      have hthree : (n + 4).choose 3 * 3 = (n + 4).choose 2 * (n + 2) := by
        simpa using Nat.choose_succ_right_eq (n + 4) 2
      have htwo : (n + 4).choose 2 * 2 = (n + 4) * (n + 3) := by
        calc
          (n + 4).choose 2 * 2 = (n + 4).choose 1 * ((n + 4) - 1) :=
            Nat.choose_succ_right_eq (n + 4) 1
          _ = (n + 4) * (n + 3) := by simp [Nat.choose_one_right]
      have hfour_real : ((n + 4).choose 4 : ℝ) * 4 =
          ((n + 4).choose 3 : ℝ) * (n + 1) := by
        exact_mod_cast hfour
      have hthree_real : ((n + 4).choose 3 : ℝ) * 3 =
          ((n + 4).choose 2 : ℝ) * (n + 2) := by
        exact_mod_cast hthree
      have htwo_real : ((n + 4).choose 2 : ℝ) * 2 =
          (n + 4 : ℝ) * (n + 3) := by
        exact_mod_cast htwo
      calc
        (24 : ℝ) * ((n + 4).choose 4 : ℝ) =
            6 * (((n + 4).choose 4 : ℝ) * 4) := by ring
        _ = 6 * (((n + 4).choose 3 : ℝ) * (n + 1)) := by rw [hfour_real]
        _ = 2 * ((((n + 4).choose 3 : ℝ) * 3) * (n + 1)) := by ring
        _ = 2 * ((((n + 4).choose 2 : ℝ) * (n + 2)) * (n + 1)) := by rw [hthree_real]
        _ = (((n + 4).choose 2 : ℝ) * 2) * (n + 2) * (n + 1) := by ring
        _ = ((n + 4 : ℝ) * (n + 3)) * (n + 2) * (n + 1) := by rw [htwo_real]
        _ = (n : ℝ) ^ 4 + 10 * n ^ 3 + 35 * n ^ 2 + 50 * n + 24 := by ring
    calc
      (n : ℝ) ^ 4 * r ^ n =
          ((24 : ℝ) * ((n + 4).choose 4 : ℝ) - 10 * n ^ 3 - 35 * n ^ 2 - 50 * n - 24) *
            r ^ n := by
              rw [hchoose]
              ring
      _ = 24 * (((n + 4).choose 4 : ℝ) * r ^ n) -
          10 * ((n : ℝ) ^ 3 * r ^ n) - 35 * ((n : ℝ) ^ 2 * r ^ n) -
          50 * ((n : ℝ) * r ^ n) - 24 * r ^ n := by ring
  · have hgap : 1 - r ≠ 0 := by linarith
    field_simp [hgap]
    ring

end AppliedModelingLib.Probability.Queueing
