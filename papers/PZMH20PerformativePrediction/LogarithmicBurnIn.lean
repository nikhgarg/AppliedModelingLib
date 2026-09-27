import AppliedModelingLib.Foundations.Optimization.PerturbedContraction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic burn-in for Theorem 3.10

The source bounds the geometric entry time using `1 - x ≤ exp (-x)`.
This file records that calculation separately from the finite-sample
concentration argument and then supplies it to the existing two-phase
contraction theorem.
-/

namespace PZMH20PerformativePrediction

/-- A natural iteration satisfying the source's logarithmic threshold makes
the corresponding geometric term no larger than the target radius. -/
theorem pow_mul_le_of_log_div_one_sub_le
    {contraction initialDistance radius : ℝ} {entryIteration : ℕ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_lt_one : contraction < 1)
    (hinitial_nonneg : 0 ≤ initialDistance)
    (hradius_pos : 0 < radius)
    (hentry : Real.log (initialDistance / radius) / (1 - contraction) ≤
      (entryIteration : ℝ)) :
    contraction ^ entryIteration * initialDistance ≤ radius := by
  by_cases hinitial_zero : initialDistance = 0
  · simp [hinitial_zero, hradius_pos.le]
  have hinitial_pos : 0 < initialDistance :=
    lt_of_le_of_ne hinitial_nonneg (Ne.symm hinitial_zero)
  have hone_sub_pos : 0 < 1 - contraction := sub_pos.mpr hcontraction_lt_one
  have hlog : Real.log (initialDistance / radius) ≤
      (entryIteration : ℝ) * (1 - contraction) := by
    exact (div_le_iff₀ hone_sub_pos).mp hentry
  have hbase_le_exp : contraction ≤ Real.exp (-(1 - contraction)) := by
    simpa only [sub_sub_cancel] using Real.one_sub_le_exp_neg (1 - contraction)
  have hpow : contraction ^ entryIteration ≤
      (Real.exp (-(1 - contraction))) ^ entryIteration :=
    pow_le_pow_left₀ hcontraction_nonneg hbase_le_exp entryIteration
  have hexp_pow : (Real.exp (-(1 - contraction))) ^ entryIteration =
      Real.exp (-((entryIteration : ℝ) * (1 - contraction))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio_pos : 0 < initialDistance / radius := div_pos hinitial_pos hradius_pos
  have hratio_le_exp : initialDistance / radius ≤
      Real.exp ((entryIteration : ℝ) * (1 - contraction)) := by
    rw [← Real.exp_log hratio_pos]
    exact Real.exp_le_exp.mpr hlog
  have hscaled_ratio :
      Real.exp (-((entryIteration : ℝ) * (1 - contraction))) *
          (initialDistance / radius) ≤ 1 := by
    calc
      Real.exp (-((entryIteration : ℝ) * (1 - contraction))) *
          (initialDistance / radius) ≤
          Real.exp (-((entryIteration : ℝ) * (1 - contraction))) *
            Real.exp ((entryIteration : ℝ) * (1 - contraction)) := by
        exact mul_le_mul_of_nonneg_left hratio_le_exp
          (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  calc
    contraction ^ entryIteration * initialDistance ≤
        Real.exp (-((entryIteration : ℝ) * (1 - contraction))) * initialDistance := by
      rw [← hexp_pow]
      exact mul_le_mul_of_nonneg_right hpow hinitial_nonneg
    _ = (Real.exp (-((entryIteration : ℝ) * (1 - contraction))) *
          (initialDistance / radius)) * radius := by
      field_simp [hradius_pos.ne']
    _ ≤ 1 * radius := mul_le_mul_of_nonneg_right hscaled_ratio hradius_pos.le
    _ = radius := one_mul radius

/-- The source logarithmic threshold is a sufficient explicit entry time for
any two-phase contraction: every later iterate remains in the target ball. -/
theorem two_phase_contraction_enters_and_stays_of_log_bound
    {distance : ℕ → ℝ} {contraction radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_lt_one : contraction < 1)
    (hinitial_nonneg : 0 ≤ distance 0)
    (hradius_pos : 0 < radius)
    (houtside : ∀ iteration, radius < distance iteration →
      distance (iteration + 1) ≤ contraction * distance iteration)
    (hinside : ∀ iteration, distance iteration ≤ radius →
      distance (iteration + 1) ≤ radius)
    (entryIteration : ℕ)
    (hentry : Real.log (distance 0 / radius) / (1 - contraction) ≤
      (entryIteration : ℝ)) :
    ∀ iteration, entryIteration ≤ iteration → distance iteration ≤ radius := by
  apply AppliedModelingLib.Optimization.two_phase_contraction_enters_and_stays
    hcontraction_nonneg houtside hinside entryIteration
  exact pow_mul_le_of_log_div_one_sub_le hcontraction_nonneg hcontraction_lt_one
    hinitial_nonneg hradius_pos hentry

end PZMH20PerformativePrediction
